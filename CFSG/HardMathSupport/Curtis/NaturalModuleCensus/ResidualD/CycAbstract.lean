module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockToralCensusBase
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabHub

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD

open CFSG.AGLEmbedding
open scoped commutatorElement

theorem false_of_cyc_two_three {Y : Type*} [Group Y] [Finite Y] {J : Subgroup Y}
    (hcyc : CycPerfect 3 J) {V : Subgroup Y} (hVJ : V ≤ J) (hV : ⁅V, V⁆ = V) {a b : Y}
    (haV : a ∈ V) (hbV : b ∈ V) (ha3 : a ^ 3 = 1) (hb3 : b ^ 3 = 1) (hcomm : Commute a b)
    (n1 : a ≠ 1) (n3 : b ≠ 1) (n5 : a ≠ b) (n6 : a * a ≠ b) : False := by
  classical
  have hS : ({a, b} : Set Y).Pairwise Commute := by
    intro u hu v hv huv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact absurd rfl huv
    · exact hcomm
    · exact hcomm.symm
    · exact absurd rfl huv
  obtain ⟨Q, hQ⟩ : ∃ Q : Subgroup Y, Q = Subgroup.closure {a, b} := ⟨_, rfl⟩
  have hQ3 : ∀ g ∈ Q, g ^ 3 = 1 := fun g hg =>
    CFSG.AGLEmbedding.ParabHub.pow_eq_one_of_mem_closure hS
      (fun u hu => by rcases hu with rfl | rfl <;> assumption) (hQ ▸ hg)
  have haQ : a ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hbQ : b ∈ Q := hQ ▸ Subgroup.subset_closure (by simp)
  have hQP : Q ≤ V := by
    rw [hQ]
    refine (Subgroup.closure_le _).2 ?_
    rintro u (rfl | rfl)
    · exact haV
    · exact hbV
  have hpg : IsPGroup 3 Q := fun g => ⟨1, Subtype.ext (by simp [hQ3 g g.2])⟩
  have hcy : IsCyclic Q := hcyc V hVJ hV Q hQP hpg
  have : Finite Q := inferInstance
  have : Fintype Q := Fintype.ofFinite Q
  have hxxQ : a * a ∈ Q := Q.mul_mem haQ haQ
  have hle := IsCyclic.card_pow_eq_one_le (α := Q) (n := 3) (by norm_num)
  have hsub : ({1, ⟨a, haQ⟩, ⟨a * a, hxxQ⟩, ⟨b, hbQ⟩} : Finset Q) ⊆
      ({g : Q | g ^ 3 = 1} : Finset Q) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Subtype.ext (hQ3 g g.2)
  have hc := Finset.card_le_card hsub
  have hxx1 : a * a ≠ 1 := by
    intro h
    apply n1
    have : a = a ^ 3 * (a * a)⁻¹ := by
      rw [pow_succ, pow_two]; group
    rw [this, ha3, h]; simp
  have hxx : a ≠ a * a := by
    intro h
    apply n1
    have : a * a = a * 1 := by rw [mul_one]; exact h.symm
    exact (mul_left_cancel this)
  have m1 : ((1 : Q)) ≠ ⟨a, haQ⟩ := fun h => n1 (by simpa using (congrArg Subtype.val h).symm)
  have m2 : ((1 : Q)) ≠ ⟨a * a, hxxQ⟩ := fun h => hxx1 (by simpa using (congrArg Subtype.val h).symm)
  have m3 : ((1 : Q)) ≠ ⟨b, hbQ⟩ := fun h => n3 (by simpa using (congrArg Subtype.val h).symm)
  have m4 : (⟨a, haQ⟩ : Q) ≠ ⟨a * a, hxxQ⟩ := fun h => hxx (congrArg Subtype.val h)
  have m5 : (⟨a, haQ⟩ : Q) ≠ ⟨b, hbQ⟩ := fun h => n5 (congrArg Subtype.val h)
  have m6 : (⟨a * a, hxxQ⟩ : Q) ≠ ⟨b, hbQ⟩ := fun h => n6 (congrArg Subtype.val h)
  rw [Finset.card_insert_of_notMem (by simp [m1, m2, m3]),
    Finset.card_insert_of_notMem (by simp [m4, m5]),
    Finset.card_insert_of_notMem (by simp [m6]), Finset.card_singleton] at hc
  omega

structure LeviIdentities {G : Type*} [Monoid G] (rh sh ra sa rb sb : G) : Prop where
  rh_sq : rh * rh = 1
  sh_sq : sh * sh = 1
  ra_sq : ra * ra = 1
  sa_sq : sa * sa = 1
  rb_sq : rb * rb = 1
  sb_sq : sb * sb = 1
  rh_eq : rh * ra * rh * ra * sa * (ra * rh * ra * rh) * sa = rh
  sh_eq : sh * sa * sh * sa * ra * (sa * sh * sa * sh) * ra = sh
  ra_eq : ra * rh * ra * rh * sh * (rh * ra * rh * ra) * sh = ra
  sa_eq : sa * sh * sa * sh * rh * (sh * sa * sh * sa) * rh = sa
  rb_eq : rb * rh * rb * rh * sh * (rh * rb * rh * rb) * sh = rb
  sb_eq : sb * sh * sb * sh * rh * (sh * sb * sh * sb) * rh = sb
  ca_pow : ra * sa * (ra * sa) * (ra * sa) = 1
  cb_pow : rb * sb * (rb * sb) * (rb * sb) = 1
  comm : ra * sa * (rb * sb) = rb * sb * (ra * sa)
  ca_ne : ra * sa ≠ 1
  cb_ne : rb * sb ≠ 1
  ca_cb : ra * sa ≠ rb * sb
  caa_cb : ra * sa * (ra * sa) ≠ rb * sb

theorem LeviIdentities.of_injective {G M : Type*} [Monoid G] [Monoid M] (ψ : G →* M)
    (hψ : Function.Injective ψ) {rh sh ra sa rb sb : G}
    (h : LeviIdentities (ψ rh) (ψ sh) (ψ ra) (ψ sa) (ψ rb) (ψ sb)) :
    LeviIdentities rh sh ra sa rb sb := by
  have key : ∀ x y : G, ψ x = ψ y → x = y := fun x y hxy => hψ hxy
  refine ⟨key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_,
    key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_, key _ _ ?_,
    key _ _ ?_, fun e => h.ca_ne ?_, fun e => h.cb_ne ?_, fun e => h.ca_cb ?_,
    fun e => h.caa_cb ?_⟩
  · simpa using h.rh_sq
  · simpa using h.sh_sq
  · simpa using h.ra_sq
  · simpa using h.sa_sq
  · simpa using h.rb_sq
  · simpa using h.sb_sq
  · simpa using h.rh_eq
  · simpa using h.sh_eq
  · simpa using h.ra_eq
  · simpa using h.sa_eq
  · simpa using h.rb_eq
  · simpa using h.sb_eq
  · simpa using h.ca_pow
  · simpa using h.cb_pow
  · simpa using h.comm
  · simpa using congrArg ψ e
  · simpa using congrArg ψ e
  · simpa using congrArg ψ e
  · simpa using congrArg ψ e

theorem mem_commutator_of_identity {G : Type*} [Group G] {P : Subgroup G} {x p q z : G}
    (hp : p * p = 1) (hq : q * q = 1) (hz : z * z = 1)
    (hpP : p ∈ P) (hqP : q ∈ P) (hzP : z ∈ P)
    (hid : p * q * p * q * z * (q * p * q * p) * z = x) : x ∈ ⁅P, P⁆ := by
  have hp' : p⁻¹ = p := inv_eq_of_mul_eq_one_right hp
  have hq' : q⁻¹ = q := inv_eq_of_mul_eq_one_right hq
  have hz' : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz
  have hcP : p * q * p * q ∈ P := P.mul_mem (P.mul_mem (P.mul_mem hpP hqP) hpP) hqP
  have h1 : ⁅p * q * p * q, z⁆ ∈ ⁅P, P⁆ := Subgroup.commutator_mem_commutator hcP hzP
  have h2 : ⁅p * q * p * q, z⁆ = x := by
    rw [commutatorElement_def, ← hid]
    simp only [mul_inv_rev, hp', hq', hz', mul_assoc]
  rwa [h2] at h1

theorem perfect_closure_of_identities {G : Type*} [Group G] {rh sh ra sa rb sb : G}
    (h : LeviIdentities rh sh ra sa rb sb) :
    ⁅Subgroup.closure {rh, sh, ra, sa, rb, sb}, Subgroup.closure {rh, sh, ra, sa, rb, sb}⁆ =
      Subgroup.closure {rh, sh, ra, sa, rb, sb} := by
  set P := Subgroup.closure ({rh, sh, ra, sa, rb, sb} : Set G) with hP
  have hrh : rh ∈ P := Subgroup.subset_closure (by simp)
  have hsh : sh ∈ P := Subgroup.subset_closure (by simp)
  have hra : ra ∈ P := Subgroup.subset_closure (by simp)
  have hsa : sa ∈ P := Subgroup.subset_closure (by simp)
  have hrb : rb ∈ P := Subgroup.subset_closure (by simp)
  have hsb : sb ∈ P := Subgroup.subset_closure (by simp)
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) ?_
  · rw [commutatorElement_def]
    exact P.mul_mem (P.mul_mem (P.mul_mem h₁ h₂) (P.inv_mem h₁)) (P.inv_mem h₂)
  · rw [hP, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl
    · exact mem_commutator_of_identity h.rh_sq h.ra_sq h.sa_sq hrh hra hsa h.rh_eq
    · exact mem_commutator_of_identity h.sh_sq h.sa_sq h.ra_sq hsh hsa hra h.sh_eq
    · exact mem_commutator_of_identity h.ra_sq h.rh_sq h.sh_sq hra hrh hsh h.ra_eq
    · exact mem_commutator_of_identity h.sa_sq h.sh_sq h.rh_sq hsa hsh hrh h.sa_eq
    · exact mem_commutator_of_identity h.rb_sq h.rh_sq h.sh_sq hrb hrh hsh h.rb_eq
    · exact mem_commutator_of_identity h.sb_sq h.sh_sq h.rh_sq hsb hsh hrh h.sb_eq

theorem false_of_cyc_levi {G Y : Type*} [Group G] [Group Y] [Finite Y] {J : Subgroup Y}
    (hcyc : CycPerfect 3 J) (Θ : G →* Y) (hΘ : Function.Injective Θ)
    {rh sh ra sa rb sb : G} (h : LeviIdentities rh sh ra sa rb sb)
    (hJ : Θ rh ∈ J ∧ Θ sh ∈ J ∧ Θ ra ∈ J ∧ Θ sa ∈ J ∧ Θ rb ∈ J ∧ Θ sb ∈ J) : False := by
  obtain ⟨j1, j2, j3, j4, j5, j6⟩ := hJ
  set P := Subgroup.closure ({rh, sh, ra, sa, rb, sb} : Set G) with hP
  have hPperf := perfect_closure_of_identities h
  have hPJ : P.map Θ ≤ J := by
    rw [Subgroup.map_le_iff_le_comap, hP, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  have hVperf : ⁅P.map Θ, P.map Θ⁆ = P.map Θ := by
    rw [← Subgroup.map_commutator, hPperf]
  have hra : ra ∈ P := Subgroup.subset_closure (by simp)
  have hsa : sa ∈ P := Subgroup.subset_closure (by simp)
  have hrb : rb ∈ P := Subgroup.subset_closure (by simp)
  have hsb : sb ∈ P := Subgroup.subset_closure (by simp)
  refine false_of_cyc_two_three hcyc hPJ hVperf (a := Θ (ra * sa)) (b := Θ (rb * sb))
    ⟨_, P.mul_mem hra hsa, rfl⟩ ⟨_, P.mul_mem hrb hsb, rfl⟩ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← map_pow, pow_succ, pow_two, h.ca_pow, map_one]
  · rw [← map_pow, pow_succ, pow_two, h.cb_pow, map_one]
  · show Θ (ra * sa) * Θ (rb * sb) = Θ (rb * sb) * Θ (ra * sa)
    rw [← map_mul, ← map_mul, h.comm]
  · intro h1
    exact h.ca_ne (hΘ (by rw [h1, map_one]))
  · intro h1
    exact h.cb_ne (hΘ (by rw [h1, map_one]))
  · intro h1
    exact h.ca_cb (hΘ h1)
  · intro h1
    exact h.caa_cb (hΘ (by rw [map_mul]; exact h1))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ResidualD
