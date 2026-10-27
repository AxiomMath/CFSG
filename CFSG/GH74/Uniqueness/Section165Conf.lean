module

public import CFSG.GH74.Uniqueness.Section164A

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec165

theorem isSylowOf_D_of_inf (S : ZDSetup X Z M) (c : Ctx16 Z M) {St : Subgroup X}
    (hSt : ABGLocalTools.IsSylowOf 2 St ((M ⊓ conjugate M c.t) ⊓ centralizer ({c.t} : Set X))) :
    ABGLocalTools.IsSylowOf 2 St (M ⊓ conjugate M c.t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hle, hp, hdvd⟩ := ABGLocalTools.isSylowOf_iff.mp hSt
  refine ABGLocalTools.isSylowOf_iff.mpr ⟨hle.trans inf_le_left, hp, ?_⟩
  rw [← Subgroup.relIndex_mul_relIndex St _ _ hle inf_le_left, Subgroup.inf_relIndex_left]
  have hodd : Odd ((centralizer ({c.t} : Set X)).relIndex (M ⊓ conjugate M c.t)) := by
    rw [(S.prodDisc.prop36d S.invariant c.ht c.htM c.hz c.hzM).2.2.1]
    exact S.odd_zNum
  intro h2
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp h2 with h | h
  · exact hdvd h
  · exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)

theorem exists_conf_four (S : ZDSetup X Z M) (c : Conf16 Z M)
    (hV : ∃ V : Subgroup X, V ≤ c.D ∧ Nat.card V = 4 ∧ ∀ v ∈ V, v * v = 1) :
    ∃ c' : Conf16 Z M, c'.D = c.D ∧ ∃ v : X, v ∈ c'.D ∧ v * v = 1 ∧ v ≠ 1 ∧
      v ≠ c'.u ∧ c'.u * v = v * c'.u ∧ v * c'.t = c'.t * v ∧ v * c'.z = c'.z * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, hVD, hV4, hV2⟩ := hV
  have hut : c.u * c.t = c.t * c.u := (mem_centralizer_singleton_iff.mp c.ht_B).symm
  have huDt : c.u ∈ c.D ⊓ centralizer ({c.t} : Set X) :=
    mem_inf.mpr ⟨c.hu, mem_centralizer_singleton_iff.mpr hut⟩
  have hu2' : IsPGroup 2 (zpowers c.u) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, c.hu2, pow_one])
  obtain ⟨St, hSt, huSt⟩ := exists_isSylowOf_ge_of_le (zpowers_le.mpr huDt) hu2'
  have huSt' : c.u ∈ St := huSt (mem_zpowers _)
  have hStD := isSylowOf_D_of_inf S c.toCtx16 hSt
  have hVp : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hV4]; norm_num)
  obtain ⟨g, -, hgV⟩ := exists_conjugate_le_of_isSylowOf hStD hVD hVp
  have hgV4 : Nat.card (conjugate V g) = 4 := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hV4]
  have hgV2 : ∀ w ∈ conjugate V g, w * w = 1 := by
    intro w hw
    have h1 := hV2 _ (mem_conjugate_iff.mp hw)
    have e : g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
    rw [e] at h1
    calc w * w = g⁻¹ * (g * (w * w) * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨v, hvSt, hv2, hv1, hvu, huv⟩ :=
    exists_commute_ne_of_four hStD.isPGroup huSt' c.hu2 hgV hgV4 hgV2
  have hvDt := hSt.le hvSt
  have hvD : v ∈ c.D := (mem_inf.mp hvDt).1
  have hvt : v * c.t = c.t * v := mem_centralizer_singleton_iff.mp (mem_inf.mp hvDt).2
  have hWBM : fourSub c.u v c.u_mul_self hv2 huv ≤ centralizer ({c.u} : Set X) ⊓ M := by
    refine fourSub_le (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr rfl, c.u_mem_M⟩) ?_
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr huv.symm, (mem_inf.mp hvD).1⟩
  have hWp : IsPGroup 2 (fourSub c.u v c.u_mul_self hv2 huv) :=
    IsPGroup.of_card (n := 2) (by rw [card_fourSub c.u_ne_one hv1 (Ne.symm hvu)]; norm_num)
  obtain ⟨T1', hT1', hWT1⟩ := exists_isSylowOf_ge_of_le hWBM hWp
  have hNK : zHull Z (centralizer ({c.u} : Set X)) ⊓ M ≤ centralizer ({c.u} : Set X) ⊓ M :=
    inf_le_inf_right M (Cor713.zHull_le _)
  have hKN : centralizer ({c.u} : Set X) ⊓ M ≤
      normalizer ((zHull Z (centralizer ({c.u} : Set X)) ⊓ M : Subgroup X) : Set X) := by
    intro x hx
    exact Sec164.mem_normalizer_inf (le_normalizer_zHull S.invariant _ (mem_inf.mp hx).1)
      (le_normalizer (mem_inf.mp hx).2)
  have hP' := hT1'.inf_of_le_normalizer hNK hKN
  obtain ⟨V', hV', hT1V', z₁, hz₁Z, hz₁M, hz₁V', hz₁c⟩ :=
    S.exists_sylow_central_ge (hT1'.le.trans inf_le_right) hT1'.isPGroup
  have huT1 : c.u ∈ T1' := mem_of_isSylowOf_centralizer c.u_mem_M c.hu2 hT1'
  have hz₁B : z₁ ∈ centralizer ({c.u} : Set X) :=
    mem_centralizer_singleton_iff.mpr (hz₁c c.u (hT1V' huT1)).symm
  have hVT1 : V' ⊓ (centralizer ({c.u} : Set X) ⊓ M) = T1' :=
    hT1'.eq_of_le (le_inf hT1V' hT1'.le) inf_le_right hV'.to_inf_left
  have hz₁T1 : z₁ ∈ T1' := by
    rw [← hVT1]
    exact mem_inf.mpr ⟨hz₁V', mem_inf.mpr ⟨hz₁B, hz₁M⟩⟩
  have hvT1 : v ∈ T1' := hWT1 (show v ∈ fourSub c.u v c.u_mul_self hv2 huv from Or.inr (Or.inr
    (Or.inl rfl)))
  refine ⟨{ t := c.t
            z := z₁
            ht := c.ht
            htM := c.htM
            hz := hz₁Z
            hzM := hz₁M
            hD := c.hD
            u := c.u
            hu := c.hu
            hu2 := c.hu2
            hmax := c.hmax
            P := T1' ⊓ (zHull Z (centralizer ({c.u} : Set X)) ⊓ M)
            T1 := T1'
            hP := hP'
            hT1 := hT1'
            hPT1 := inf_le_left
            ht_B := c.ht_B
            hz_T1 := ⟨hz₁T1, fun y hy => hz₁c y (hT1V' hy)⟩ }, rfl, v, hvD, hv2, hv1, hvu,
    huv, hvt, hz₁c v (hT1V' hvT1)⟩

end Sec165

end CFSG.GH74.Uniqueness
