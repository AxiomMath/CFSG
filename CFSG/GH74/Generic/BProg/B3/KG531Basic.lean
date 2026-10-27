module

public import CFSG.GH74.Generic.BProg.B3.KG531Crit
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvAltInv
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4McL
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3EvenA
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4L3U3
public import CFSG.GH74.GLS.IVK.Proofs2.GHInvExcShape
public import CFSG.GH74.Generic.S1.KL5LyRee

public section

namespace CFSG.GH74.Generic.BProg.B3

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped MatrixGroups

theorem KG531Cfg.false_of_comp_top {S : Type} [Group S] {t : S} {B₁ B₂ : Subgroup S} {p f : ℕ}
    (h : KG531Cfg t B₁ B₂ p f) {C₀ : Type} [Group C₀]
    (φ : ↥(centralizer ({t} : Set S)) ≃* C₀)
    (hC₀ : ∀ K : Subgroup C₀, CFSG.IsComponent K → K = ⊤) : False := by
  refine h.false_of_star fun B hB => ?_
  have hmap := hC₀ _ (CFSG.LocalCores.isComponent_map_mulEquiv φ hB.2)
  have htop : B.subgroupOf (centralizer ({t} : Set S)) = ⊤ := by
    apply Subgroup.map_injective (f := φ.toMonoidHom) φ.injective
    rw [hmap, Subgroup.map_top_of_surjective _ φ.surjective]
  have ht : (⟨t, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩ :
      ↥(centralizer ({t} : Set S))) ∈ B.subgroupOf (centralizer ({t} : Set S)) := by
    rw [htop]
    exact Subgroup.mem_top _
  exact ht

namespace KG531Basic

theorem alt_false {n : ℕ} (hn : n ≤ 11) {x : alternatingGroup (Fin n)} (hx2 : x * x = 1)
    (hx1 : x ≠ 1) {L : Subgroup (alternatingGroup (Fin n))} (hL : Group.IsPerfect ↥L)
    (hLc : ∀ y ∈ L, y * x = x * y) (hxL : x ∈ L) : False := by
  set σ : Equiv.Perm (Fin n) := (x : Equiv.Perm (Fin n)) with hσdef
  have hσ : σ * σ = 1 := by
    have := congrArg Subtype.val hx2
    simpa [σ] using this
  have hσ1 : ∃ a, σ a ≠ a := by
    by_contra hcon
    push Not at hcon
    apply hx1
    apply Subtype.ext
    exact Equiv.ext fun a => hcon a
  obtain ⟨hsupp, hsign⟩ := CFSG.GH74.GLS.IVK.GHInv.involution_cycle_data hσ
  have hsign1 : Equiv.Perm.sign σ = 1 := Equiv.Perm.mem_alternatingGroup.1 x.2
  have hle : σ.support.card ≤ 11 := by
    calc σ.support.card ≤ Finset.univ.card := Finset.card_le_univ _
      _ = n := by simp
      _ ≤ 11 := hn
  have hkeven : Even σ.cycleType.card := by
    rw [hsign] at hsign1
    exact (neg_one_pow_eq_one_iff_even (by decide)).1 hsign1
  have hc : σ.cycleType.card ≤ 4 := by
    obtain ⟨j, hj⟩ := hkeven
    omega
  have := hL
  have hP : Group.IsPerfect ↥(L.map (alternatingGroup (Fin n)).subtype) :=
    Group.IsPerfect.map _
  have hPc : ∀ y ∈ L.map (alternatingGroup (Fin n)).subtype, y * σ = σ * y := by
    rintro _ ⟨k, hk, rfl⟩
    exact congrArg Subtype.val (hLc k hk)
  obtain ⟨a, ha⟩ := hσ1
  exact ha (CFSG.GH74.GLS.IVK.GHInv.perfect_fixes_support hσ hc hP hPc σ ⟨x, hxL, rfl⟩ a ha)

end KG531Basic

theorem kg531_alt (n : ℕ) (_h7 : 7 ≤ n) (h11 : n ≤ 11) :
    KG531Empty (fun X _ => Nonempty (X ≃* alternatingGroup (Fin n))) := by
  intro S _ _ hS hnab hSA t B₁ B₂ p f h
  obtain ⟨e⟩ := hSA
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.t_ord]
    exact pow_orderOf_eq_one t
  have hx2 : e t * e t = 1 := by rw [← map_mul, ht2, map_one]
  have hx1 : e t ≠ 1 := by
    intro h1
    have h1' : t = 1 := e.injective (by rw [h1, map_one])
    have := h.t_ord
    rw [h1', orderOf_one] at this
    omega
  refine h.false_of_perfect fun P hPle hP ht => ?_
  have hperf : Group.IsPerfect ↥(P.map e.toMonoidHom) := by
    have := hP
    exact Group.IsPerfect.map _
  refine KG531Basic.alt_false h11 hx2 hx1 hperf ?_ ⟨t, ht, rfl⟩
  rintro _ ⟨k, hk, rfl⟩
  have hkt := Subgroup.mem_centralizer_singleton_iff.1 (hPle hk)
  show e k * e t = e t * e k
  rw [← map_mul, ← map_mul, hkt]

open CFSG.Sporadic.Schreier CFSG.Sporadic.SmallOddCore in
theorem kg531_mcl :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .McL) := by
  intro S _ _ hS hnab hSp t B₁ B₂ p f h
  obtain ⟨e⟩ := hSp
  let e' : S ≃* ↥mclP := e.trans mclPermEquiv
  have hord : orderOf ((e' t : ↥mclP) : Equiv.Perm (Fin 275)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.t_ord
  obtain ⟨g, hg, hgt⟩ := (mclT0_facts).2.2.2.2 _ (e' t).2 hord
  exact h.false_of_comp_top (CFSG.GH74.GLS.IVK.GHInv.centralizerEquivConj mclP e' t hg hgt)
    fun K hK => CFSG.GH74.GLS.IVK.mclCt_isComponent_top hK

open CFSG.Sporadic.Schreier CFSG.ClassicalInvolution CFSG.Sporadic.Ly in
theorem kg531_ly :
    KG531Empty (fun X _ => NativeSporadic.IsSporadic X .Ly) := by
  obtain ⟨hkey, hq, -, -⟩ := LyProof.K_facts
  obtain ⟨hSp, hidx⟩ := LyProof.S_sylow
  obtain ⟨-, hcover⟩ := LyProof.S_facts
  have hperf : Group.IsPerfect ↥LyProof.KJ := Group.isPerfect_def.2 hq.1
  intro S _ _ hS hnab hSL t B₁ B₂ p f h
  obtain ⟨e⟩ := hSL
  let e' : S ≃* ↥J := e.trans lyEquivJ
  have hord : orderOf (e' t) = 2 := by
    rw [MulEquiv.orderOf_eq]
    exact h.t_ord
  have hSr : ∀ s ∈ LyProof.SJ, orderOf s = 2 →
      ∃ c ∈ (⊤ : Subgroup J), s = c * LyProof.zJ * c⁻¹ := by
    intro s hs hso
    have hss : s * s = 1 := by
      have := pow_orderOf_eq_one s
      rwa [hso, pow_two] at this
    have hs1 : s ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hso
      exact absurd hso (by norm_num)
    obtain ⟨C, hC⟩ := hcover s hs hss hs1
    exact ⟨C, Subgroup.mem_top C, hC⟩
  obtain ⟨c, -, hc⟩ := cover_of_sylow (⊤ : Subgroup J) LyProof.SJ hSp hidx LyProof.zJ hSr (e' t)
    (Subgroup.mem_top _) hord
  refine h.false_of_comp_top (C₀ := ↥LyProof.KJ) ?_ fun K hK => ?_
  · exact (CFSG.GH74.GLS.IVK.GHInv.centralizerEquivConj
      (J : Subgroup (GL (Fin 111) (ZMod 5))) e' t
      (t := ((LyProof.zJ : J) : GL (Fin 111) (ZMod 5)))
      (g := (c : GL (Fin 111) (ZMod 5))) c.2 (by rw [hc]; simp)).trans
      ((CFSG.GH74.GLS.IVK.GHInv.centralizerSubtypeEquiv J LyProof.zJ).symm.trans
        (MulEquiv.subgroupCongr hkey))
  · exact CFSG.GH74.GLS.IVK.GHInv.isComponent_eq_top_of_perfect hperf
      (QuotientGroup.mk' (center ↥LyProof.KJ)) (QuotientGroup.mk'_surjective _) hq.2
      (by rw [QuotientGroup.ker_mk']) hK

theorem kg531_ree
    (f : ℕ) :
    KG531Empty (fun X _ => LieModel X .twistedG2 0 3 f) := by
  intro S _ _ hS hnab hRee t B₁ B₂ p f' h
  have hq := CFSG.GH74.Generic.S1.kl5_odd_pow (f := f') h.prime h.odd
  have hpow : p ^ (2 * f') = (p ^ f') ^ 2 := by rw [← pow_mul, mul_comm]
  have h32 : 32 ∣ (p ^ f' * (p ^ (2 * f') - 1) / 2) * (p ^ f' * (p ^ (2 * f') - 1)) := by
    rw [hpow]
    exact KG531Crit.thirty_two_dvd_expr hq
  have h16 : 16 ∣ Nat.card S :=
    ((show 16 ∣ 32 by norm_num).trans h32).trans
      (h.card_dvd.trans (Subgroup.card_subgroup_dvd_card _))
  exact CFSG.GH74.Generic.S1.kl5_false_ree hRee h16

namespace KG531Basic

theorem le_expr {p f : ℕ} (h5 : 5 ≤ p ^ f) :
    7200 ≤ (p ^ f * (p ^ (2 * f) - 1) / 2) * (p ^ f * (p ^ (2 * f) - 1)) := by
  have hpow : p ^ (2 * f) = (p ^ f) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hpow]
  generalize p ^ f = q at h5 ⊢
  have h1 : 24 ≤ q ^ 2 - 1 := by
    have := Nat.pow_le_pow_left h5 2
    omega
  have h2 : 120 ≤ q * (q ^ 2 - 1) := Nat.mul_le_mul h5 h1
  have h3 : 60 ≤ q * (q ^ 2 - 1) / 2 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by omega)
  exact Nat.mul_le_mul h3 h2

end KG531Basic

theorem KG531Cfg.false_of_card_lt {S : Type} [Group S] [Finite S] {t : S}
    {B₁ B₂ : Subgroup S} {p f : ℕ} (h : KG531Cfg t B₁ B₂ p f) {N : ℕ} (hN : Nat.card S = N)
    (hN7 : N < 7200) : False := by
  have hd := h.card_dvd.trans (Subgroup.card_subgroup_dvd_card _)
  rw [hN] at hd
  have hpos : 0 < N := hN ▸ Nat.card_pos
  have := Nat.le_of_dvd hpos hd
  have := KG531Basic.le_expr h.five
  omega

theorem kg531_l3 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .PSL 3 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  have hX : StatedClassicalModel S .PSL 3 p f :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.t_ord]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.t_ord
    rw [h1, orderOf_one] at this
    omega
  by_cases h5 : 5 ≤ p ^ f
  · exact h.false_of_star fun B hB =>
      CFSG.GH74.GLS.IVK.comp_mem_lin_all hp hp2 h5 hX t ht2 ht1 B hB
  · have hp3 : p = 3 := by
      have h2 := hp.two_le
      have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with h' | h' | h'
      · exact absurd h' hp2
      · exact h'
      · subst h'
        norm_num at hp
    have hf1 : f = 1 := by
      subst hp3
      by_contra hne
      have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hp3
    subst hf1
    have hc := CFSG.GH74.card_of_lieModel_PSL (n := 3) (by norm_num) hL
    exact h.false_of_card_lt (N := 5616) (hc.trans (by decide)) (by norm_num)

theorem kg531_u3 (p f : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .PSU 3 p f) := by
  intro S _ _ hS hnab hL t B₁ B₂ p' f' h
  have hX : StatedClassicalModel S .PSU 3 p f :=
    CFSG.GH74.statedClassicalModel_of_lieModel (by norm_num) hL
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← h.t_ord]
    exact pow_orderOf_eq_one t
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.t_ord
    rw [h1, orderOf_one] at this
    omega
  by_cases h5 : 5 ≤ p ^ f
  · exact h.false_of_star fun B hB =>
      CFSG.GH74.GLS.IVK.comp_mem_uni hp hp2 h5 hX t ht2 ht1 B hB
  · have hp3 : p = 3 := by
      have h2 := hp.two_le
      have hpf : p ≤ p ^ f := Nat.le_self_pow (by omega) p
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with h' | h' | h'
      · exact absurd h' hp2
      · exact h'
      · subst h'
        norm_num at hp
    have hf1 : f = 1 := by
      subst hp3
      by_contra hne
      have : 3 ^ 2 ≤ 3 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    subst hp3
    subst hf1
    have hc := CFSG.GH74.card_of_lieModel_PSU (n := 3) (by norm_num) hp2 hL
    exact h.false_of_card_lt (N := 6048) (hc.trans (by decide)) (by norm_num)

theorem kg531_g2 (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .G2 0 p f) := by
  intro S _ _ hS hnab hG t B₁ B₂ p' f' h
  exact h.false_of_star fun B hB =>
    CFSG.GH74.GLS.IVK.GHInv.mem_of_isCompIn_G2 hp hp2 hG hf t h.t_ord hB

theorem kg531_d4 (p f : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (hf : 1 ≤ f) :
    KG531Empty (fun X _ => LieModel X .trialityD4 0 p f) := by
  intro S _ _ hS hnab hD t B₁ B₂ p' f' h
  exact h.false_of_star fun B hB =>
    CFSG.GH74.GLS.IVK.GHInv.mem_of_isCompIn_D4 hp hp2 hD hf t h.t_ord hB

end CFSG.GH74.Generic.BProg.B3
