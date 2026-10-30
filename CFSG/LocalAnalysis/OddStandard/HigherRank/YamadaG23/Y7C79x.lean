module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y54
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y7Defs

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Open CFSG.OddStandard.HigherRank.G2Three
  CFSG.OddStandard.HigherRank.G2Three.Sec1
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem y7c_order7_fpf_aux {F : Subgroup G} (hF : Nat.card F = 8) {x : G}
    (hx : x ^ 7 = 1) (hn : ∀ f ∈ F, x * f * x⁻¹ ∈ F) (hnc : ∃ f ∈ F, x * f * x⁻¹ ≠ f)
    {f : G} (hf : f ∈ F) (hfx : x * f * x⁻¹ = f) : f = 1 := by
  classical
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : Fintype ↥F := Fintype.ofFinite ↥F
  let g : Function.End ↥F := fun y => ⟨x * (y : G) * x⁻¹, hn (y : G) y.2⟩
  have hg_apply : ∀ y : ↥F, (g y : G) = x * (y : G) * x⁻¹ := fun _ => rfl
  have hiter : ∀ n : ℕ, ∀ y : ↥F, ((g^[n]) y : G) = x ^ n * (y : G) * (x ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro y; rw [Function.iterate_zero_apply, pow_zero]; simp
    | succ n ih =>
        intro y
        rw [Function.iterate_succ_apply', hg_apply (g^[n] y), ih y]
        group
  have hg7 : g ^ 7 = 1 := by
    funext y
    apply Subtype.ext
    show ((g^[7]) y : G) = (y : G)
    rw [hiter 7 y, hx]
    simp
  have hcardF : Fintype.card ↥F = 8 :=
    (Nat.card_eq_fintype_card (α := ↥F)).symm.trans hF
  have hmod : 8 ≡ Fintype.card g.fixedPoints [MOD 7] := by
    have h := Equiv.Perm.card_fixedPoints_modEq (f := g) (p := 7) (n := 1) hg7
    rwa [hcardF] at h
  obtain ⟨w, hwF, hwne⟩ := hnc
  have hw_notfix : ¬ (⟨w, hwF⟩ : ↥F) ∈ g.fixedPoints := by
    rw [Function.mem_fixedPoints_iff]
    intro h
    exact hwne (by
      have h' := congrArg (Subtype.val) h
      rwa [hg_apply ⟨w, hwF⟩] at h')
  have hk_lt : Fintype.card g.fixedPoints < 8 := by
    have h := Fintype.card_subtype_lt (p := fun y : ↥F => y ∈ g.fixedPoints)
      (x := (⟨w, hwF⟩ : ↥F)) hw_notfix
    rwa [hcardF] at h
  have hk_le : Fintype.card g.fixedPoints ≤ 7 := by omega
  have hk_mod : Fintype.card g.fixedPoints % 7 = 1 := by
    have h := hmod
    rw [Nat.ModEq] at h
    have h8 : 8 % 7 = 1 := by norm_num
    rw [h8] at h
    exact h.symm
  have hk_eq : Fintype.card g.fixedPoints = 1 := by
    have hlt7 : Fintype.card g.fixedPoints < 7 := by
      rcases lt_or_ge (Fintype.card g.fixedPoints) 7 with h | h
      · exact h
      · have h7 : Fintype.card g.fixedPoints = 7 := le_antisymm hk_le h
        rw [h7] at hk_mod
        norm_num at hk_mod
    rw [Nat.mod_eq_of_lt hlt7] at hk_mod
    exact hk_mod
  by_contra hfne
  have htwo : 2 ≤ Fintype.card g.fixedPoints := by
    let a : g.fixedPoints := ⟨1, by
      rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; rw [hg_apply]; simp⟩
    let b : g.fixedPoints := ⟨⟨f, hf⟩, by
      rw [Function.mem_fixedPoints_iff]; apply Subtype.ext; rw [hg_apply]; exact hfx⟩
    have hab : a ≠ b := by
      intro hab
      apply hfne
      have h := congrArg (fun z : g.fixedPoints => ((z : ↥F) : G)) hab
      simpa [a, b] using h.symm
    have h1lt : 1 < Fintype.card g.fixedPoints := Fintype.one_lt_card_iff.mpr ⟨a, b, hab⟩
    omega
  omega

private theorem y7c_commutator_self_le (A : Subgroup G) : ⁅A, A⁆ ≤ A := by
  rw [Subgroup.commutator_le]
  intro g₁ h₁ g₂ h₂
  rw [commutatorElement_def]
  exact A.mul_mem (A.mul_mem (A.mul_mem h₁ h₂) (A.inv_mem h₁)) (A.inv_mem h₂)

theorem y7c_JF_le_L (s : Setting3 G L) : JF s ≤ L := by
  rw [JF]
  exact (y7c_commutator_self_le (normIn L s.fr.F)).trans inf_le_left

theorem y7c_JF_comm_t (s : Setting3 G L) : ∀ j ∈ JF s, j * s.t = s.t * j :=
  fun j hj => s3_comm_t_of_mem_L s (y7c_JF_le_L s hj)

theorem y7c_JF_le_K7 (s : Setting3 G L) : JF s ≤ K7 s := by
  rw [K7]
  refine le_trans ?_ (le_iSup₂_of_le (1 : G) (Subgroup.one_mem _) le_rfl)
  intro j hj
  rw [conjSub, Subgroup.mem_map]
  exact ⟨j, Subgroup.mem_sup_left hj, by simp [MulAut.conj_apply]⟩

theorem y7c_JF_norm_F (s : Setting3 G L) : ∀ x ∈ JF s, ∀ f ∈ s.fr.F, x * f * x⁻¹ ∈ s.fr.F := by
  intro x hx f hf
  have hxN : x ∈ normIn L s.fr.F := y7c_commutator_self_le (normIn L s.fr.F) hx
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.mem_inf.mp hxN).2 f).mp hf

theorem y7c_card_JF {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    Nat.card ↥(JF s) = 1344 := by
  have hN : normIn L s.fr.F = JF s := by
    have h := hH.hLF.fact18.2.2.2.2.2.2.1.1
    rw [f3_zL_eq_bot hH, sup_bot_eq] at h
    show normIn L s.fr.F = ⁅normIn L s.fr.F, normIn L s.fr.F⁆
    exact h
  rw [← hN]
  exact y54_card_N hH

theorem y7c_exists_order7 {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) :
    ∃ x ∈ JF s, x ^ 7 = 1 ∧ x ≠ 1 := by
  have h7 : 7 ∣ Nat.card ↥(JF s) := by rw [y7c_card_JF hH]; norm_num
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(JF s)) 7 h7
  refine ⟨(x : G), x.2, ?_, ?_⟩
  · have h : x ^ 7 = 1 := by rw [← hx]; exact pow_orderOf_eq_one x
    simpa using congrArg (Subtype.val) h
  · intro hxG
    have hxsub : x = 1 := Subtype.ext hxG
    rw [hxsub, orderOf_one] at hx
    omega

theorem y7c_order7_not_cent {s : Setting3 G L} {e : Setting3.Ext s} (hH : F33Hyp s e) {x : G}
    (hx : x ∈ JF s) (hx7 : x ^ 7 = 1) (hx1 : x ≠ 1) : ∃ f ∈ s.fr.F, x * f * x⁻¹ ≠ f := by
  by_contra h
  push Not at h
  have hxL : x ∈ L := y7c_JF_le_L s hx
  have h1 : ∀ f ∈ s.fr.F, x * f = f * x := by
    intro f hf
    calc x * f = x * f * x⁻¹ * x := by group
      _ = f * x := by rw [h f hf]
  have hxF : x ∈ s.fr.F := by
    rw [← y54_centIn_L_F hH]
    exact Subgroup.mem_inf.mpr
      ⟨hxL, Subgroup.mem_centralizer_iff.mpr (fun f hf => (h1 f hf).symm)⟩
  have hx2 : x ^ 2 = 1 := y54_F_sq hH x hxF
  have h1 : orderOf x = 1 := by
    have hd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
    have hd7 : orderOf x ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hx7
    have hg := Nat.dvd_gcd hd hd7
    simpa using hg
  exact hx1 (orderOf_eq_one_iff.mp h1)

theorem y7c_centIn_M3_JF (c : Ctx5 G L) (hH : F33Hyp c.s c.e) :
    centIn (M3 c.s) (JF c.s) = ⊥ := by
  classical
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  obtain ⟨hmM3, hmCent⟩ := Subgroup.mem_inf.mp hm
  obtain ⟨x, hxJ, hx7, hx1⟩ := y7c_exists_order7 hH
  have hnc := y7c_order7_not_cent hH hxJ hx7 hx1
  have hF8 : Nat.card ↥c.s.fr.F = 8 := by simpa using (y54_F_isE3 hH).2
  have hxL : x ∈ L := y7c_JF_le_L c.s hxJ
  have hxnormF : ∀ f ∈ c.s.fr.F, x * f * x⁻¹ ∈ c.s.fr.F := y7c_JF_norm_F c.s x hxJ
  have hxH : x ∈ c.s.H := by
    rw [Setting3.H]
    exact Subgroup.mem_centralizer_iff.mpr (fun h hh => by
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (s3_comm_t_of_mem_L c.s hxL).symm)
  have hxN : x ∈ normIn c.s.H c.s.fr.F :=
    Subgroup.mem_inf.mpr ⟨hxH,
      (Subgroup.mem_inf.mp (y7c_commutator_self_le (normIn L c.s.fr.F) hxJ)).2⟩
  have hxm : x * m * x⁻¹ = m := by
    have h2 : x * m = m * x := Subgroup.mem_centralizer_iff.mp hmCent x hxJ
    rw [h2, mul_assoc, mul_inv_cancel, mul_one]
  obtain ⟨hNsub, hP⟩ := (y54_fact c hH).1.2.2.2
  letI := hNsub
  obtain ⟨φ, hφ⟩ := hP
  let m₀ : ↥(M3 c.s) := ⟨m, hmM3⟩
  have heq := hφ x hxN m₀ m₀ hxm.symm
  have hfix :
      ((φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m₀) : ↥c.s.fr.F) : G) = 1 :=
    y7c_order7_fpf_aux hF8 hx7 hxnormF hnc
      (φ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s)) m₀)).2 heq.symm
  have hpi := (MulEquiv.map_eq_one_iff φ).mp (Subtype.ext hfix)
  have hmF : m ∈ c.s.fr.F := by
    have h : m₀ ∈ (QuotientGroup.mk' (c.s.fr.F.subgroupOf (M3 c.s))).ker :=
      MonoidHom.mem_ker.mpr hpi
    rw [QuotientGroup.ker_mk', Subgroup.mem_subgroupOf] at h
    exact h
  exact y7c_order7_fpf_aux hF8 hx7 hxnormF hnc hmF hxm

end CFSG.OddStandard.HigherRank.YamadaG23
