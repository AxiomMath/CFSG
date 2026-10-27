module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Wrap

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup
open scoped commutatorElement

variable {Y : Type} [Group Y]

@[expose] def conjSub (n : Y) (P : Subgroup Y) : Subgroup Y := P.map (MulAut.conj n).toMonoidHom

theorem mem_conjSub {n : Y} {P : Subgroup Y} {x : Y} :
    x ∈ conjSub n P ↔ ∃ p ∈ P, n * p * n⁻¹ = x := by
  simp [conjSub, MulAut.conj_apply]

structure KD309Cfg (P : Subgroup Y) (z : Y) (J : Subgroup Y) (n g h : Y) : Prop where
  J_le : J ≤ P
  J_abel : CFSG.Open.IsElemAbelian 5 J
  J_card : Nat.card J = 5 ^ 4
  E_card : Nat.card (⁅J, P⁆ : Subgroup Y) = 5 ^ 3
  z_mem : z ∈ ⁅J, P⁆
  n_J : n ∈ normalizer (J : Set Y)
  n_E : n ∈ normalizer ((⁅J, P⁆ : Subgroup Y) : Set Y)
  g_mem : g ∈ P
  g_not : g ∉ J
  h_mem : h ∈ conjSub n P
  h_not : h ∉ J
  conj_g : IsConj z g
  conj_h : IsConj z h
  irr : ∀ S : Subgroup Y, S ≤ P ⊔ conjSub n P → S.relIndex (P ⊔ conjSub n P) ≤ 5 →
    ∀ F : Subgroup Y, F ≤ ⁅J, P⁆ → (∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F) → F = ⊥ ∨ F = ⁅J, P⁆

theorem le_normalizer_of_conj {K F : Subgroup Y} (h : ∀ k ∈ K, ∀ f ∈ F, k * f * k⁻¹ ∈ F) :
    K ≤ normalizer (F : Set Y) := by
  intro k hk
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => h k hk y hy, fun hy => ?_⟩
  have := h k⁻¹ (K.inv_mem hk) _ hy
  simpa [mul_assoc] using this

theorem conj_mem_commutator {J P : Subgroup Y} {p : Y} (hpJ : ∀ j ∈ J, p * j * p⁻¹ ∈ J)
    (hpP : ∀ x ∈ P, p * x * p⁻¹ ∈ P) : ∀ e ∈ ⁅J, P⁆, p * e * p⁻¹ ∈ ⁅J, P⁆ := by
  intro e he
  rw [Subgroup.commutator_def] at he
  refine Subgroup.closure_induction (p := fun e _ => p * e * p⁻¹ ∈ ⁅J, P⁆) ?_ ?_ ?_ ?_ he
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    have : p * ⁅a, b⁆ * p⁻¹ = ⁅p * a * p⁻¹, p * b * p⁻¹⁆ := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact Subgroup.commutator_mem_commutator (hpJ a ha) (hpP b hb)
  · simp
  · intro x y _ _ hx hy
    have : p * (x * y) * p⁻¹ = (p * x * p⁻¹) * (p * y * p⁻¹) := by group
    rw [this]
    exact mul_mem hx hy
  · intro x _ hx
    have : p * x⁻¹ * p⁻¹ = (p * x * p⁻¹)⁻¹ := by group
    rw [this]
    exact inv_mem hx

theorem eq_sup_zpowers {J P : Subgroup Y} [Finite Y] (hJP : J ≤ P)
    (hcard : Nat.card P = 5 * Nat.card J) {g : Y} (hgP : g ∈ P) (hgJ : g ∉ J) :
    P = J ⊔ zpowers g := by
  set K := J ⊔ zpowers g with hK
  have hKP : K ≤ P := sup_le hJP (zpowers_le.mpr hgP)
  have hJK : J ≤ K := le_sup_left
  obtain ⟨t, ht⟩ := Subgroup.card_dvd_of_le hJK
  obtain ⟨s, hs⟩ := Subgroup.card_dvd_of_le hKP
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hts : t * s = 5 := by
    have h1 : Nat.card J * (t * s) = Nat.card J * 5 := by
      rw [← mul_assoc, ← ht, ← hs, hcard, mul_comm]
    exact Nat.eq_of_mul_eq_mul_left hJpos h1
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, mul_one] at ht
    have hJK' : J = K := Subgroup.eq_of_le_of_card_ge hJK (by rw [ht])
    apply hgJ
    rw [hJK']
    exact Subgroup.mem_sup_right (mem_zpowers g)
  have ht5 : t = 5 := by
    have hdvd : t ∣ 5 := ⟨s, hts.symm⟩
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd h ht1
    · exact h
  have hs1 : s = 1 := by
    rw [ht5] at hts
    omega
  have hKcard : Nat.card K = Nat.card P := by rw [hs, hs1, mul_one]
  exact (Subgroup.eq_of_le_of_card_ge hKP (by rw [hKcard])).symm


theorem endgame_cfg [Finite Y] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] (ρ : Representation (ZMod 2) Y V) {P J : Subgroup Y}
    {z n g h : Y} (hP : IsPGroup 5 P) (hPcard : Nat.card P = 5 ^ 5)
    (hJn : ∀ p ∈ P, ∀ j ∈ J, p * j * p⁻¹ ∈ J) (cfg : KD309Cfg P z J n g h)
    (hρz : ρ z ≠ 1)
    (hdim : Module.finrank (ZMod 2) (commSub ρ (Subgroup.closure
      ({z, n * z * n⁻¹, g, h} : Set Y))) ≤ 36) : False := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨hJP, hJe, hJcard, hEcard, hzE, hnJ', hnE', hgP, hgJ, hhQ, hhJ, -, -, hirr⟩ := cfg
  set E : Subgroup Y := ⁅J, P⁆ with hE
  set Q : Subgroup Y := conjSub n P with hQ
  set N₁ : Subgroup Y := P ⊔ Q with hN₁
  set N₀ : Subgroup Y := Subgroup.closure ({z, n * z * n⁻¹, g, h} : Set Y) with hN₀
  have hnJ : ∀ y, y ∈ J ↔ n * y * n⁻¹ ∈ J := Subgroup.mem_normalizer_iff.mp hnJ'
  have hnE : ∀ y, y ∈ E ↔ n * y * n⁻¹ ∈ E := Subgroup.mem_normalizer_iff.mp hnE'
  have hJcomm : ∀ a ∈ J, ∀ b ∈ J, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hJe.1.is_comm.comm (⟨a, ha⟩ : J) ⟨b, hb⟩)
  have hEJ : E ≤ J := by
    rw [hE, Subgroup.commutator_le]
    intro j hj p hp
    have : ⁅j, p⁆ = j * (p * j⁻¹ * p⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [this]
    exact J.mul_mem hj (hJn p hp j⁻¹ (J.inv_mem hj))
  have hJ' : ∀ y, n⁻¹ * y * n ∈ J ↔ y ∈ J := fun y => by
    rw [hnJ (n⁻¹ * y * n)]
    simp [mul_assoc]
  have hE' : ∀ y, n⁻¹ * y * n ∈ E ↔ y ∈ E := fun y => by
    rw [hnE (n⁻¹ * y * n)]
    simp [mul_assoc]
  have hcardP : Nat.card P = 5 * Nat.card J := by rw [hPcard, hJcard]; norm_num
  have hQcard : Nat.card Q = Nat.card P := Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hJQ : J ≤ Q := fun j hj => mem_conjSub.mpr ⟨n⁻¹ * j * n, hJP ((hJ' j).mpr hj), by group⟩
  have hPeq : P = J ⊔ zpowers g := eq_sup_zpowers hJP hcardP hgP hgJ
  have hQeq : Q = J ⊔ zpowers h := eq_sup_zpowers hJQ (by rw [hQcard]; exact hcardP) hhQ hhJ
  have hzJ : z ∈ J := hEJ hzE
  have hzP : z ∈ P := hJP hzJ
  have hz'E : n * z * n⁻¹ ∈ E := (hnE z).mp hzE
  have hz'Q : n * z * n⁻¹ ∈ Q := mem_conjSub.mpr ⟨z, hzP, rfl⟩
  have hz'J : n * z * n⁻¹ ∈ J := hEJ hz'E
  have hN₀N : N₀ ≤ N₁ := by
    rw [hN₀, Subgroup.closure_le]
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.mem_sup_left hzP
    · exact Subgroup.mem_sup_right hz'Q
    · exact Subgroup.mem_sup_left hgP
    · exact Subgroup.mem_sup_right hhQ
  have hgN₀ : g ∈ N₀ := Subgroup.subset_closure (by simp)
  have hhN₀ : h ∈ N₀ := Subgroup.subset_closure (by simp)
  have hzN₀ : z ∈ N₀ := Subgroup.subset_closure (by simp)
  have hN₁le : N₁ ≤ J ⊔ N₀ := by
    refine sup_le ?_ ?_
    · rw [hPeq]
      exact sup_le_sup_left (zpowers_le.mpr hgN₀) J
    · rw [hQeq]
      exact sup_le_sup_left (zpowers_le.mpr hhN₀) J
  have hJN₁ : J ≤ N₁ := hJP.trans le_sup_left
  have hQJ : ∀ q ∈ Q, ∀ j ∈ J, q * j * q⁻¹ ∈ J := by
    intro q hq j hj
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hq
    have h1 : n⁻¹ * j * n ∈ J := (hJ' j).mpr hj
    have h2 := hJn p hp _ h1
    have h3 := (hnJ _).mp h2
    have : n * p * n⁻¹ * j * (n * p * n⁻¹)⁻¹ = n * (p * (n⁻¹ * j * n) * p⁻¹) * n⁻¹ := by group
    rw [this]
    exact h3
  have hPE : ∀ p ∈ P, ∀ e ∈ E, p * e * p⁻¹ ∈ E := fun p hp e he =>
    conj_mem_commutator (J := J) (P := P) (hJn p hp)
      (fun x hx => P.mul_mem (P.mul_mem hp hx) (P.inv_mem hp)) e he
  have hQE : ∀ q ∈ Q, ∀ e ∈ E, q * e * q⁻¹ ∈ E := by
    intro q hq e he
    obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hq
    have h1 : n⁻¹ * e * n ∈ E := (hE' e).mpr he
    have h2 := hPE p hp _ h1
    have h3 := (hnE _).mp h2
    have : n * p * n⁻¹ * e * (n * p * n⁻¹)⁻¹ = n * (p * (n⁻¹ * e * n) * p⁻¹) * n⁻¹ := by group
    rw [this]
    exact h3
  have hN₁J : N₁ ≤ normalizer (J : Set Y) :=
    sup_le (le_normalizer_of_conj hJn) (le_normalizer_of_conj hQJ)
  have hN₁E : N₁ ≤ normalizer (E : Set Y) :=
    sup_le (le_normalizer_of_conj hPE) (le_normalizer_of_conj hQE)
  have hJn₁ : ∀ x ∈ N₁, ∀ j ∈ J, x * j * x⁻¹ ∈ J := fun x hx j hj =>
    ((Subgroup.mem_normalizer_iff.mp (hN₁J hx)) j).mp hj
  have hEn₁ : ∀ x ∈ N₁, ∀ e ∈ E, x * e * x⁻¹ ∈ E := fun x hx e he =>
    ((Subgroup.mem_normalizer_iff.mp (hN₁E hx)) e).mp he
  have hcomm : ∀ m ∈ N₀, ∀ j ∈ J, m * j * m⁻¹ * j⁻¹ ∈ E := by
    intro m hm
    refine Subgroup.closure_induction (p := fun m _ => ∀ j ∈ J, m * j * m⁻¹ * j⁻¹ ∈ E)
      ?_ ?_ ?_ ?_ hm
    · intro x hx j hj
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl | rfl
      · rw [hJcomm _ hzJ j hj]
        simp
      · rw [hJcomm _ hz'J j hj]
        have h1 : j * (n * z * n⁻¹) * (n * z * n⁻¹)⁻¹ * j⁻¹ = 1 := by group
        rw [h1]
        exact E.one_mem
      · have h1 : ⁅j, x⁆ ∈ E := Subgroup.commutator_mem_commutator hj hgP
        have h2 := E.inv_mem h1
        convert h2 using 1
        simp only [commutatorElement_def]
        group
      · obtain ⟨p, hp, rfl⟩ := mem_conjSub.mp hhQ
        have h1 : ⁅n⁻¹ * j * n, p⁆ ∈ E := Subgroup.commutator_mem_commutator ((hJ' j).mpr hj) hp
        have h2 := (hnE _).mp (E.inv_mem h1)
        convert h2 using 1
        simp only [commutatorElement_def]
        group
    · intro j hj
      simp
    · intro x y hx hy hxj hyj j hj
      have hxN : x ∈ N₁ := hN₀N hx
      have h1 := hEn₁ x hxN _ (hyj j hj)
      have h2 := E.mul_mem h1 (hxj j hj)
      convert h2 using 1
      group
    · intro x hx hxj j hj
      have hxN : x⁻¹ ∈ N₁ := N₁.inv_mem (hN₀N hx)
      have h1 := hxj (x⁻¹ * j * x) (by simpa using hJn₁ x⁻¹ hxN j hj)
      have h2 := E.inv_mem h1
      convert h2 using 1
      group
  have hFnorm : N₁ ≤ normalizer ((N₀ ⊓ E : Subgroup Y) : Set Y) := by
    refine hN₁le.trans (sup_le ?_ ?_)
    · refine le_normalizer_of_conj fun j hj f hf => ?_
      rw [hJcomm j hj f (hEJ hf.2)]
      simpa using hf
    · refine le_normalizer_of_conj fun m hm f hf => ⟨N₀.mul_mem (N₀.mul_mem hm hf.1)
        (N₀.inv_mem hm), hEn₁ m (hN₀N hm) f hf.2⟩
  have hz1 : z ≠ 1 := by
    rintro rfl
    exact hρz (map_one ρ)
  have hEN₀ : E ≤ N₀ := by
    rcases hirr N₁ le_rfl (by rw [Subgroup.relIndex_self]; norm_num) (N₀ ⊓ E) inf_le_right
        (fun s hs f hf => ((Subgroup.mem_normalizer_iff.mp (hFnorm hs)) f).mp hf) with h | h
    · exfalso
      have hzF : z ∈ N₀ ⊓ E := ⟨hzN₀, hzE⟩
      rw [h, Subgroup.mem_bot] at hzF
      exact hz1 hzF
    · exact h ▸ inf_le_left
  have hN₀n : ∀ x ∈ N₁, ∀ m ∈ N₀, x * m * x⁻¹ ∈ N₀ := by
    have : N₁ ≤ normalizer (N₀ : Set Y) := by
      refine hN₁le.trans (sup_le ?_ Subgroup.le_normalizer)
      refine le_normalizer_of_conj fun j hj m hm => ?_
      have h1 := hEN₀ (E.inv_mem (hcomm m hm j hj))
      have h2 := N₀.mul_mem h1 hm
      convert h2 using 1
      group
    exact fun x hx m hm => ((Subgroup.mem_normalizer_iff.mp (this hx)) m).mp hm
  exact endgame_Y ρ (N₁ := N₁) (N₀ := N₀) hP hJP hJe hJcard hEJ hEcard le_rfl le_sup_left hJn₁
    hEn₁ hN₀N hN₀n hEN₀ hirr hzE hρz hdim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
