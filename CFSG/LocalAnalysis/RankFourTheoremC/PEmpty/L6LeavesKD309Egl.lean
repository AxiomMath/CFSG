module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Faith
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKD309Grp
public import CFSG.GroupTheory.HyperplaneDecomposition
public import CFSG.Quasithin.EmptyFaithful.SzN31CntLinA
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import TauCeti.LinearAlgebra.Dimension.DirectSum

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309

open Subgroup CFSG.SolvableHall
open scoped commutatorElement Pointwise

variable {G W : Type} [Group G] [Finite G] [AddCommGroup W] [Module (ZMod 2) W]

noncomputable abbrev Fx (ρ : Representation (ZMod 2) G W) (B : Subgroup G) :
    Submodule (ZMod 2) W :=
  Representation.invariants (ρ.comp B.subtype)

theorem mem_Fx {ρ : Representation (ZMod 2) G W} {B : Subgroup G} {w : W} :
    w ∈ Fx ρ B ↔ ∀ b ∈ B, ρ b w = w :=
  mem_invariants_comp_subtype

theorem map_Fx_le (ρ : Representation (ZMod 2) G W) (n : G) (B : Subgroup G) :
    letI := subConjAction G
    (Fx ρ B).map (repEquiv ρ n : W →ₗ[ZMod 2] W) ≤ Fx ρ (n • B) := by
  letI := subConjAction G
  rintro _ ⟨v, hv, rfl⟩
  refine mem_Fx.mpr fun b hb => ?_
  have hb' : n⁻¹ * b * n ∈ B := (mem_conj_subgroup_iff n B b).mp hb
  have h1 := mem_Fx.mp hv _ hb'
  change ρ b (ρ n v) = ρ n v
  have h2 : ρ b (ρ n v) = ρ n (ρ (n⁻¹ * b * n) v) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    group
  rw [h2, h1]

theorem finrank_Fx_conj [Finite W] (ρ : Representation (ZMod 2) G W) (n : G) (B : Subgroup G) :
    letI := subConjAction G
    Module.finrank (ZMod 2) (Fx ρ (n • B)) = Module.finrank (ZMod 2) (Fx ρ B) := by
  letI := subConjAction G
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have h1 : Module.finrank (ZMod 2) (Fx ρ B) ≤ Module.finrank (ZMod 2) (Fx ρ (n • B)) := by
    have := Submodule.finrank_mono (map_Fx_le ρ n B)
    rwa [LinearEquiv.finrank_map_eq (repEquiv ρ n)] at this
  have h2 : Module.finrank (ZMod 2) (Fx ρ (n • B)) ≤ Module.finrank (ZMod 2) (Fx ρ B) := by
    have h3 := Submodule.finrank_mono (map_Fx_le ρ n⁻¹ (n • B))
    rw [LinearEquiv.finrank_map_eq (repEquiv ρ n⁻¹)] at h3
    have h4 : n⁻¹ • (n • B) = B := inv_smul_smul n B
    rwa [h4] at h3
  exact le_antisymm h2 h1


theorem card_hyperplane {J B : Subgroup G} (hBJ : B ≤ J) (hrel : B.relIndex J = 5)
    (hJcard : Nat.card J = 5 ^ 4) : Nat.card B = 5 ^ 3 := by
  have h := Subgroup.relIndex_mul_card (H := B) (K := J)
  rw [hrel, inf_eq_left.mpr hBJ, hJcard] at h
  have h5 : (5 : ℕ) ^ 4 = 5 * 5 ^ 3 := by norm_num
  rw [h5] at h
  exact Nat.eq_of_mul_eq_mul_left (by norm_num) h

theorem four_le_finrank_Fx [Finite W] (ρ : Representation (ZMod 2) G W) {J B : Subgroup G}
    (hJe : CFSG.Open.IsElemAbelian 5 J) (hFJ : Fx ρ J = ⊥) (hBJ : B ≤ J)
    (hrel : B.relIndex J = 5) (hB : Fx ρ B ≠ ⊥) : 4 ≤ Module.finrank (ZMod 2) (Fx ρ B) := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hnle : ¬ J ≤ B := by
    intro h
    have := Subgroup.relIndex_eq_one.mpr h
    omega
  obtain ⟨j, hjJ, hjB⟩ : ∃ j ∈ J, j ∉ B := by
    by_contra hcon
    push Not at hcon
    exact hnle hcon
  have hsup : B ⊔ zpowers j = J := by
    have hle : B ⊔ zpowers j ≤ J := sup_le hBJ (zpowers_le.mpr hjJ)
    have hdvd : (B ⊔ zpowers j).relIndex J ∣ 5 := by
      rw [← hrel]
      exact Subgroup.relIndex_dvd_of_le_left J le_sup_left
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact le_antisymm hle (Subgroup.relIndex_eq_one.mp h1)
    · exfalso
      have hc : ∀ C : Subgroup G, C ≤ J → C.relIndex J = 5 → 5 * Nat.card C = Nat.card J := by
        intro C hCJ hC
        have h := Subgroup.relIndex_mul_card (H := C) (K := J)
        rwa [hC, inf_eq_left.mpr hCJ] at h
      have h1 := hc B hBJ hrel
      have h2 := hc (B ⊔ zpowers j) hle h5
      have heq : B = B ⊔ zpowers j := Subgroup.eq_of_le_of_card_ge le_sup_left
        (by have := Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 5) (h1.trans h2.symm); omega)
      apply hjB
      rw [heq]
      exact Subgroup.mem_sup_right (mem_zpowers j)
  let x : W ≃ₗ[ZMod 2] W := repEquiv ρ j
  have hx : x ^ 5 = 1 := by
    have := hJe.2 j hjJ
    have h2 := congrArg (repEquiv ρ) this
    rwa [map_pow, map_one] at h2
  have hcomm : ∀ b ∈ B, b * j = j * b := fun b hb =>
    congrArg Subtype.val (hJe.1.is_comm.comm (⟨b, hBJ hb⟩ : J) (⟨j, hjJ⟩ : J))
  have hxT : ∀ t ∈ Fx ρ B, x t ∈ Fx ρ B := by
    intro t ht
    refine mem_Fx.mpr fun b hb => ?_
    change ρ b (ρ j t) = ρ j t
    rw [← Module.End.mul_apply, ← map_mul, hcomm b hb, map_mul, Module.End.mul_apply,
      mem_Fx.mp ht b hb]
  have h0 : ∀ t ∈ Fx ρ B, x t = t → t = 0 := by
    intro t ht hxt
    have hj' : ρ j t = t := hxt
    have htz : t ∈ Fx ρ (zpowers j) := mem_Fx.mpr fun h hh => fixed_of_mem_zpowers hj' hh
    have h1 : t ∈ Representation.invariants (ρ.comp (B ⊔ zpowers j).subtype) := by
      rw [invariants_comp_subtype_sup]
      exact ⟨ht, htz⟩
    change t ∈ Fx ρ (B ⊔ zpowers j) at h1
    rw [hsup, hFJ] at h1
    simpa using h1
  have hdvd := CFSG.Quasithin.SzN31.cyclic_dvd_two_pow Nat.prime_five x hx (Fx ρ B) hxT h0
  have hpos : 0 < Module.finrank (ZMod 2) (Fx ρ B) := by
    haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
    exact Nat.pos_of_ne_zero fun h => hB (Submodule.finrank_eq_zero.mp h)
  by_contra hlt
  push Not at hlt
  generalize Module.finrank (ZMod 2) (Fx ρ B) = d at hdvd hpos hlt
  interval_cases d <;> omega


theorem endgame_core [Finite W] [Nontrivial W] (ρ : Representation (ZMod 2) G W)
    {P J E : Subgroup G} (hP : IsPGroup 5 P) (hJP : J ≤ P)
    (hJe : CFSG.Open.IsElemAbelian 5 J) (hJcard : Nat.card J = 5 ^ 4)
    (hJn : ∀ g : G, ∀ j ∈ J, g * j * g⁻¹ ∈ J)
    (hEJ : E ≤ J) (hEcard : Nat.card E = 5 ^ 3) (hEn : ∀ g : G, ∀ e ∈ E, g * e * g⁻¹ ∈ E)
    (hEP : E ≤ ⁅J, P⁆)
    (hirr : ∀ S : Subgroup G, S.index ≤ 5 → ∀ F : Subgroup G, F ≤ E →
      (∀ s ∈ S, ∀ f ∈ F, s * f * s⁻¹ ∈ F) → F = ⊥ ∨ F = E)
    (hdim : Module.finrank (ZMod 2) W ≤ 36)
    (hfix : ∀ w : W, (∀ e ∈ E, ρ e w = w) → w = 0) : False := by
  classical
  letI := subConjAction G
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Module.Finite (ZMod 2) W := Module.Finite.of_finite
  have h2p : Nat.Prime 2 := Nat.prime_two
  have h5p : Nat.Prime 5 := Nat.prime_five
  have hJbot : J ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hJcard
    norm_num at hJcard
  have hFJ : Fx ρ J = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    exact hfix w fun e he => mem_Fx.mp hw e (hEJ he)
  have hindep := iSupIndep_invariants_hyperplanes ρ h2p h5p (by norm_num) hJe hFJ
  have hspan := iSup_invariants_hyperplanes_eq_top ρ h2p h5p (by norm_num) hJe hJbot
  haveI hJnorm : J.Normal := ⟨fun j hj g => hJn g j hj⟩
  have hFE : Fx ρ E = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro w hw
    exact hfix w fun e he => mem_Fx.mp hw e he
  obtain ⟨B₁, hB₁J, hB₁rel, hB₁⟩ : ∃ B : Subgroup G, B ≤ J ∧ B.relIndex J = 5 ∧ Fx ρ B ≠ ⊥ := by
    by_contra hall
    push Not at hall
    have h1 : (⨆ B : {B : Subgroup G // B ≤ J ∧ B.relIndex J = 5}, Fx ρ B.1) = ⊥ := by
      exact iSup_eq_bot.mpr fun B => hall B.1 B.2.1 B.2.2
    have h2 : (⨆ B : {B : Subgroup G // B ≤ J ∧ B.relIndex J = 5}, Fx ρ B.1) = ⊤ := hspan
    rw [h1] at h2
    exact bot_ne_top h2
  have hd4 := four_le_finrank_Fx ρ hJe hFJ hB₁J hB₁rel hB₁
  have hcardB : ∀ B : Subgroup G, B ≤ J → B.relIndex J = 5 → Nat.card B = 5 ^ 3 :=
    fun B hBJ hrel => card_hyperplane hBJ hrel hJcard
  let O : Set (Subgroup G) := MulAction.orbit G B₁
  have hO : ∀ B ∈ O, B ≤ J ∧ B.relIndex J = 5 := by
    rintro _ ⟨n, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      have h1 := (mem_conj_subgroup_iff n B₁ x).mp hx
      have h2 := hJn n _ (hB₁J h1)
      simpa [mul_assoc] using h2
    · have h := Subgroup.relIndex_pointwise_smul (MulAut.conj n) B₁ J
      rw [Subgroup.Normal.conj_smul_eq_self n J] at h
      exact h.trans hB₁rel
  have hOfin : Finite O := Set.toFinite O
  have hdimO : ∀ B ∈ O, Module.finrank (ZMod 2) (Fx ρ B) = Module.finrank (ZMod 2) (Fx ρ B₁) := by
    rintro _ ⟨n, rfl⟩
    exact finrank_Fx_conj ρ n B₁
  have hsum : Nat.card O * Module.finrank (ZMod 2) (Fx ρ B₁) ≤ 36 := by
    haveI : Fintype O := Fintype.ofFinite O
    let fam : O → Submodule (ZMod 2) W := fun B => Fx ρ B.1
    let emb : O → {B : Subgroup G // B ≤ J ∧ B.relIndex J = 5} :=
      fun B => ⟨B.1, hO B.1 B.2⟩
    have hembinj : Function.Injective emb := fun a b h =>
      Subtype.ext (congrArg (fun x : {B : Subgroup G // B ≤ J ∧ B.relIndex J = 5} => x.1) h)
    have hind : iSupIndep fam := hindep.comp hembinj
    have h1 := TauCeti.finrank_iSup_eq_sum_finrank_of_iSupIndep hind
    have h2 : Module.finrank (ZMod 2) (⨆ i, fam i : Submodule (ZMod 2) W) ≤
        Module.finrank (ZMod 2) W := Submodule.finrank_le _
    rw [h1] at h2
    have h3 : ∀ B : O, Module.finrank (ZMod 2) (fam B) = Module.finrank (ZMod 2) (Fx ρ B₁) :=
      fun B => hdimO B.1 B.2
    simp only [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card]
      at h2
    omega
  have hOle : Nat.card O ≤ 9 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  let T' : SubMulAction P (Subgroup G) :=
    ⟨O, fun g x hx => by
      obtain ⟨n, rfl⟩ := hx
      exact ⟨(g : G) * n, by
        show ((g : G) * n) • B₁ = (g : G) • (n • B₁)
        exact mul_smul _ _ _⟩⟩
  have hnofix : ∀ x : T', x ∉ MulAction.fixedPoints P T' := by
    intro x hxfix
    have hxO : x.1 ∈ O := x.2
    have hxJ := hO x.1 hxO
    have hxn : ∀ p ∈ P, ∀ b ∈ x.1, p * b * p⁻¹ ∈ x.1 := by
      intro p hp b hb
      have h1 : (⟨p⁻¹, P.inv_mem hp⟩ : P) • x = x := hxfix ⟨p⁻¹, P.inv_mem hp⟩
      have h2 : p⁻¹ • x.1 = x.1 := congrArg Subtype.val h1
      have h3 : b ∈ p⁻¹ • x.1 := by rw [h2]; exact hb
      have h4 := (mem_conj_subgroup_iff p⁻¹ x.1 b).mp h3
      simpa using h4
    have hcomm := comm_le_of_normalized hP hJP hxJ.1
      (fun p hp j hj => hJn p j hj) hxn (by rw [hcardB _ hxJ.1 hxJ.2, hJcard]; norm_num)
    have hEx : E ≤ x.1 := hEP.trans hcomm
    have hEeq : E = x.1 := Subgroup.eq_of_le_of_card_ge hEx (by rw [hEcard, hcardB _ hxJ.1 hxJ.2])
    have hF : Fx ρ x.1 = ⊥ := by rw [← hEeq]; exact hFE
    have hfr : Module.finrank (ZMod 2) (Fx ρ x.1) = Module.finrank (ZMod 2) (Fx ρ B₁) :=
      hdimO x.1 hxO
    rw [hF, finrank_bot] at hfr
    omega
  have h5dvd : 5 ∣ Nat.card O := by
    haveI : Finite T' := hOfin
    have hmod := hP.card_modEq_card_fixedPoints T'
    have hempty : IsEmpty (MulAction.fixedPoints P T') :=
      ⟨fun x => hnofix x.1 x.2⟩
    have h0 : Nat.card (MulAction.fixedPoints P T') = 0 := Nat.card_of_isEmpty
    rw [h0] at hmod
    exact (Nat.modEq_zero_iff_dvd).mp hmod
  have hOpos : 0 < Nat.card O := by
    haveI : Nonempty O := ⟨⟨B₁, MulAction.mem_orbit_self B₁⟩⟩
    exact Nat.card_pos
  have hO5 : Nat.card O = 5 := by
    obtain ⟨k, hk⟩ := h5dvd
    omega
  have hidx : (MulAction.stabilizer G B₁).index = 5 := by
    rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq]
    exact hO5
  have hB₁card := hcardB B₁ hB₁J hB₁rel
  have hinvariant : ∀ s ∈ MulAction.stabilizer G B₁, ∀ f ∈ B₁ ⊓ E, s * f * s⁻¹ ∈ B₁ ⊓ E := by
    intro s hs f hf
    refine ⟨?_, hEn s f hf.2⟩
    have hs' : s⁻¹ ∈ MulAction.stabilizer G B₁ := inv_mem hs
    have h1 : s⁻¹ • B₁ = B₁ := hs'
    have h2 : f ∈ s⁻¹ • B₁ := by rw [h1]; exact hf.1
    have h3 := (mem_conj_subgroup_iff s⁻¹ B₁ f).mp h2
    simpa using h3
  rcases hirr (MulAction.stabilizer G B₁) (le_of_eq hidx) (B₁ ⊓ E) inf_le_right hinvariant with
    h | h
  ·
    have hc : ∀ x ∈ B₁, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
      congrArg Subtype.val (hJe.1.is_comm.comm (⟨x, hB₁J hx⟩ : J) (⟨y, hEJ hy⟩ : J))
    have h1 := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute B₁ E hc).1
    rw [h, Subgroup.card_bot, mul_one, hB₁card, hEcard] at h1
    have h2 : Nat.card (B₁ ⊔ E : Subgroup G) ≤ Nat.card J :=
      Subgroup.card_le_of_le (sup_le hB₁J hEJ)
    rw [hJcard, h1] at h2
    norm_num at h2
  ·
    have hEB : E ≤ B₁ := h ▸ inf_le_left
    have hEeq : E = B₁ := Subgroup.eq_of_le_of_card_ge hEB (by rw [hEcard, hB₁card])
    exact hB₁ (by rw [← hEeq]; exact hFE)

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KD309
