module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82CIA0L
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog82P29A
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TPropM
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TNat
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10TPerm
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Sylow
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2C
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2J
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsL2Rank
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSp4Sec8
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB82A10SideS6

public section

namespace CFSG.ComponentClassification.GSThmB.A10T

open CFSG Subgroup Equiv Equiv.Perm CFSG.ComponentClassification.UnbalancedLayer
open CFSG.ComponentClassification.GSThmB.Catalog82A10 CFSG.ComponentClassification.GSThmB.P29.A10
open CFSG.ComponentClassification.GSThmB.Eight2

variable {X : Type} [Group X] [Finite X]

abbrev fixZ : Finset (Fin 10) := {0, 1, 2, 3, 8, 9}

structure Ctx (X : Type) [Group X] [Finite X] extends Eight2.CtxA0 X where
  hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))
  ι : s.h.subQuot s.y →* Perm (Fin 10)
  ι_injective : Function.Injective ι
  ι_mem_alt : ∀ u, u ∈ generalizedFitting (s.h.subQuot s.y) ↔ ι u ∈ alternatingGroup (Fin 10)
  alt_le_range : alternatingGroup (Fin 10) ≤ ι.range
  ι_a : ι s.sec.a = sigmaTwo
  map_J : s.sec.J.map ι = altOn fixTwo
  map_S : s.sec.S.map ι = P ⊓ ι.range

private theorem conj_mem_altOn_fixTwo {g x : Perm (Fin 10)} (hg : g * sigmaTwo = sigmaTwo * g)
    (hx : x ∈ altOn fixTwo) : g * x * g⁻¹ ∈ altOn fixTwo := by
  obtain ⟨hxA, hxS⟩ := mem_altOn.mp hx
  refine mem_altOn.mpr
    ⟨(inferInstance : (alternatingGroup (Fin 10)).Normal).conj_mem x hxA g, ?_⟩
  rw [Perm.support_conj]
  intro j hj
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  exact (A10Side.mem_fixTwo_iff_of_commute hg i).mpr (hxS hi)

private theorem exists_normal_emb (s : Setting2 X)
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    ∃ ι : s.h.subQuot s.y →* Perm (Fin 10), IsEmb ι ∧ ι s.sec.a = sigmaTwo ∧
      s.sec.J.map ι = altOn fixTwo ∧ s.sec.S.map ι = P ⊓ ι.range := by
  obtain ⟨e⟩ := hA
  obtain ⟨-, φ, hφ, hφι⟩ := exists_normal_form s.hp s.hp2 s.hf s.centralizer_eq e
    s.sec.orderOf_a s.sec.J_le s.sec.isPComponent_J s.J_type
  have hJφ : s.sec.J.map φ = altOn fixTwo := by
    have h := map_eq_altOn φ hφ.1 hφ.2.1 s.sec.a s.sec.J s.sec.J_le s.sec.isPComponent_J
      (by rw [hφι, card_support_sigmaTwo])
    rwa [hφι, support_sigmaTwo_compl] at h
  have hCN : centralizer ({s.sec.a} : Set (s.h.subQuot s.y)) ≤
      normalizer (s.sec.J : Set (s.h.subQuot s.y)) := by
    intro g hg
    have hg' : φ g * sigmaTwo = sigmaTwo * φ g := by
      rw [← hφι, ← map_mul, ← map_mul, mem_centralizer_singleton_iff.mp hg]
    refine Eight2.mem_normalizer_of_conj_mem_fin fun j hj => ?_
    have h1 : φ (g * j * g⁻¹) ∈ s.sec.J.map φ := by
      rw [hJφ, map_mul, map_mul, map_inv]
      exact conj_mem_altOn_fixTwo hg' (hJφ ▸ mem_map_of_mem φ hj)
    obtain ⟨k, hk, hkj⟩ := mem_map.mp h1
    rwa [← hφ.1 hkj]
  have hS : Seven.IsSylowIn s.sec.S (centralizer ({s.sec.a} : Set (s.h.subQuot s.y))) := by
    have hle := s.sec.S_le
    have hsyl := s.sec.S_sylow
    rw [inf_eq_left.mpr hCN] at hle hsyl
    exact ⟨hle, hsyl⟩
  obtain ⟨g, hg, hS'⟩ := P29.exists_conj_map_eq φ hφ.1 hS (P := P)
    (by rw [hφι]; exact P_le_centralizer) isPGroup_P (by rw [hφι, relIndex_P]; decide)
  set ψ := (MulAut.conj g).toMonoidHom.comp φ with hψdef
  have hψι : ψ s.sec.a = sigmaTwo := by
    rw [hφι] at hg
    rw [hψdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφι,
      ← mem_centralizer_iff.mp hg sigmaTwo rfl, mul_inv_cancel_right]
  have hJψ : s.sec.J.map ψ = altOn fixTwo := by
    have h := map_eq_altOn ψ (hφ.conj g).1 (hφ.conj g).2.1 s.sec.a s.sec.J s.sec.J_le
      s.sec.isPComponent_J (by rw [hψι, card_support_sigmaTwo])
    rwa [hψι, support_sigmaTwo_compl] at h
  exact ⟨ψ, hφ.conj g, hψι, hJψ, hS'⟩

theorem exists_ctx {s : Setting3 X}
    (hN : normalizer (s.h.S : Set X) ≤ centralizer ({s.h.a} : Set X))
    (hA : Nonempty (↥(generalizedFitting (s.h.subQuot s.y)) ≃* alternatingGroup (Fin 10))) :
    ∃ c : Ctx X, c.s.toSetting1 = s.toSetting1 := by
  obtain ⟨s', hs', htL, ht2⟩ := s.exists_setting3_Lay
  have hh : s'.h = s.h := congrArg (fun u : Setting1 X => u.h) hs'
  have hy : s'.y = s.y := congrArg (fun u : Setting1 X => u.y) hs'
  rw [← hh] at hN
  rw [← hh, ← hy] at htL ht2 hA
  obtain ⟨Z⟩ := exists_zData AutL2Facts.cfL2Sylow AutL2Facts.cfL2C AutL2Facts.cfL2J
    AutL2Facts.cfL2Rank CatFactsSp4.cfSec8JOrder s'.case8 s'.center_J
  obtain ⟨b, hbB, hbb, hzb⟩ := s'.exists_b Z
  obtain ⟨ι, ⟨hinj, hrange, halt⟩, hιa, hJ, hS⟩ := exists_normal_emb s'.toSetting2 hA
  exact ⟨
    { s := s'
      Z := Z
      b := b
      htL := htL
      ht2 := ht2
      hN := hN
      hbB := hbB
      hbb := hbb
      hzb := hzb
      hA := hA
      ι := ι
      ι_injective := hinj
      ι_mem_alt := halt
      alt_le_range := hrange
      ι_a := hιa
      map_J := hJ
      map_S := hS }, hs'⟩

namespace Ctx

variable (c : Ctx X)

@[expose] noncomputable def φ : ↥(c.s.h.secSub c.s.y) →* Perm (Fin 10) :=
  c.ι.comp (c.s.h.subQ c.s.y)

private theorem φ_apply (w : ↥(c.s.h.secSub c.s.y)) : c.φ w = c.ι (c.s.h.subQ c.s.y w) := rfl

theorem φ_eq_one_of_mem_B0 {w : ↥(c.s.h.secSub c.s.y)} (hw : (w : X) ∈ c.s.h.secB0 c.s.y) :
    c.φ w = 1 := by
  rw [φ_apply, Hyp52.subQ_eq_one_of_mem_secB0 hw, map_one]

theorem mem_B0_of_φ_eq_one {w : ↥(c.s.h.secSub c.s.y)} {k : ℕ} (hw : (w : X) ^ 2 ^ k = 1)
    (h1 : c.φ w = 1) : (w : X) ∈ c.s.h.secB0 c.s.y := by
  refine Hyp52.subQ_eq_one_of_two hw (c.ι_injective ?_)
  rw [map_one, ← φ_apply]
  exact h1

theorem φ_a : c.φ ⟨c.s.h.a, c.s.secCond.a_mem_secSub⟩ = sigmaTwo := by
  rw [φ_apply, ← c.s.sec_a c.s.secCond.a_mem_secSub, c.ι_a]

theorem z_mem_S0 : c.Z.z ∈ c.s.h.S ⊓ c.s.h.secG0 c.s.y :=
  mem_inf.mpr ⟨c.s.h.D_le_S c.Z.hzD, c.s.D_le_G0 c.Z.hzD⟩

theorem z_mem_secSub : c.Z.z ∈ c.s.h.secSub c.s.y :=
  c.s.h.S_inf_le_secSub c.s.y c.z_mem_S0

private theorem U0_eq :
    U0 = (c.s.sec.S ⊓ generalizedFitting (c.s.h.subQuot c.s.y)).map c.ι := by
  apply le_antisymm
  · intro u hu
    obtain ⟨huP, huA⟩ := mem_inf.mp hu
    obtain ⟨v, rfl⟩ := c.alt_le_range huA
    have hvS : v ∈ c.s.sec.S := by
      have h1 : c.ι v ∈ c.s.sec.S.map c.ι := by
        rw [c.map_S]
        exact mem_inf.mpr ⟨huP, ⟨v, rfl⟩⟩
      obtain ⟨w, hw, hwv⟩ := mem_map.mp h1
      rwa [← c.ι_injective hwv]
    exact mem_map_of_mem _ (mem_inf.mpr ⟨hvS, (c.ι_mem_alt v).mpr huA⟩)
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨hvS, hvF⟩ := mem_inf.mp hv
    have h1 : c.ι v ∈ c.s.sec.S.map c.ι := mem_map_of_mem _ hvS
    rw [c.map_S] at h1
    exact mem_inf.mpr ⟨(mem_inf.mp h1).1, (c.ι_mem_alt v).mp hvF⟩

private theorem U0_le_map_S0' :
    U0 ≤ ((c.s.h.S ⊓ c.s.h.secG0 c.s.y).subgroupOf (c.s.h.secSub c.s.y)).map c.φ := by
  rw [c.U0_eq]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨w, hw, rfl⟩ := mem_map.mp (c.s.inf_genFitting_le_map_S0 hv)
  exact mem_map_of_mem _ (mem_subgroupOf.mpr
    (mem_inf.mpr ⟨mem_subgroupOf.mp hw, c.s.h.secSub_le_G0 c.s.y w.2⟩))

private theorem φ_z_conj : (c.φ ⟨c.s.t, c.s.t_H⟩)⁻¹ * c.φ ⟨c.Z.z, c.z_mem_secSub⟩ *
    c.φ ⟨c.s.t, c.s.t_H⟩ = sigmaTwo := by
  have hb : c.φ ⟨c.b, c.s.h.secB0_le_secSub c.s.y c.hbB⟩ = 1 := c.φ_eq_one_of_mem_B0 c.hbB
  have h1 : (⟨c.s.t, c.s.t_H⟩ : ↥(c.s.h.secSub c.s.y))⁻¹ * ⟨c.Z.z, c.z_mem_secSub⟩ *
      ⟨c.s.t, c.s.t_H⟩ = ⟨c.s.h.a, c.s.secCond.a_mem_secSub⟩ *
        ⟨c.b, c.s.h.secB0_le_secSub c.s.y c.hbB⟩ := Subtype.ext c.hzb
  have h2 := congrArg c.φ h1
  rwa [map_mul, map_mul, map_inv, map_mul, c.φ_a, hb, mul_one] at h2

private theorem φ_z_eq : c.φ ⟨c.Z.z, c.z_mem_secSub⟩ =
    c.φ ⟨c.s.t, c.s.t_H⟩ * sigmaTwo * (c.φ ⟨c.s.t, c.s.t_H⟩)⁻¹ := by
  rw [← c.φ_z_conj]
  group

theorem φ_z : c.φ ⟨c.Z.z, c.z_mem_secSub⟩ = z0 := by
  set w := c.φ ⟨c.Z.z, c.z_mem_secSub⟩ with hw
  have hcent : ∀ u ∈ U0, w * u = u * w := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := mem_map.mp (c.U0_le_map_S0' hu)
    have hzv : c.Z.z * (v : X) = (v : X) * c.Z.z :=
      (c.Z.hzS _ (mem_inf.mp (mem_subgroupOf.mp hv)).1).symm
    rw [hw, ← map_mul, ← map_mul]
    exact congrArg c.φ (Subtype.ext hzv)
  have hE := (mem_centralizer_U0_iff w).mp hcent
  have hcard : w.support.card = 4 := by
    rw [hw, c.φ_z_eq, Perm.card_support_conj]
    exact card_support_sigmaTwo
  have hne : w ≠ sigmaTwo := by
    intro h
    have haH := c.s.secCond.a_mem_secSub
    have haa : c.s.h.a * c.s.h.a = 1 := Six.a_mul_a_self c.s.h
    have hw1 : c.φ (⟨c.s.h.a, haH⟩ * ⟨c.Z.z, c.z_mem_secSub⟩) = 1 := by
      rw [map_mul, c.φ_a, ← hw, h]
      decide
    have hw2 : ((⟨c.s.h.a, haH⟩ * ⟨c.Z.z, c.z_mem_secSub⟩ : ↥(c.s.h.secSub c.s.y)) : X) ^ 2 ^ 1
        = 1 := by
      change (c.s.h.a * c.Z.z) ^ 2 ^ 1 = 1
      rw [pow_one, pow_two, mul_assoc, ← mul_assoc c.Z.z, c.toCtxA0.hza, mul_assoc, c.Z.hzz,
        mul_one, haa]
    have hB := c.mem_B0_of_φ_eq_one hw2 hw1
    apply c.Z.hzP
    have he : c.Z.z = c.s.h.a * (c.s.h.a * c.Z.z) := by rw [← mul_assoc, haa, one_mul]
    rw [he]
    exact mul_mem c.s.h.a_mem_P (c.s.B0_le_P hB)
  simp only [E8, Finset.mem_insert, Finset.mem_singleton] at hE
  rcases hE with h | h | h | h | h | h | h | h
  · rw [h] at hcard
    exact absurd hcard (by decide)
  · exact absurd h hne
  · exact h
  all_goals
    rw [h] at hcard
    exact absurd hcard (by decide)

theorem φ_t_conj : c.φ ⟨c.s.t, c.s.t_H⟩ * sigmaTwo * (c.φ ⟨c.s.t, c.s.t_H⟩)⁻¹ = z0 ∧
    c.φ ⟨c.s.t, c.s.t_H⟩ * z0 * (c.φ ⟨c.s.t, c.s.t_H⟩)⁻¹ = sigmaTwo := by
  set T := c.φ ⟨c.s.t, c.s.t_H⟩ with hT
  have h1 : T * sigmaTwo * T⁻¹ = z0 := by rw [← c.φ_z, c.φ_z_eq]
  refine ⟨h1, ?_⟩
  have haH := c.s.secCond.a_mem_secSub
  have htt : (⟨c.s.t, c.s.t_H⟩ * ⟨c.s.t, c.s.t_H⟩ : ↥(c.s.h.secSub c.s.y)) *
      ⟨c.s.h.a, haH⟩ = ⟨c.s.h.a, haH⟩ * (⟨c.s.t, c.s.t_H⟩ * ⟨c.s.t, c.s.t_H⟩) :=
    Subtype.ext (c.s.h.comm_a (mem_inf.mp c.ht2).1)
  have h2 := congrArg c.φ htt
  simp only [map_mul] at h2
  rw [c.φ_a, ← hT] at h2
  calc T * z0 * T⁻¹ = (T * T * sigmaTwo) * (T * T)⁻¹ := by rw [← h1]; group
    _ = sigmaTwo := by rw [h2]; group

theorem U0_le_map_S0 :
    U0 ≤ ((c.s.h.S ⊓ c.s.h.secG0 c.s.y).subgroupOf (c.s.h.secSub c.s.y)).map c.φ :=
  c.U0_le_map_S0'

theorem φ_t_normalizes_U0 :
    ∀ u ∈ U0, c.φ ⟨c.s.t, c.s.t_H⟩ * u * (c.φ ⟨c.s.t, c.s.t_H⟩)⁻¹ ∈ U0 := by
  have : (generalizedFitting (c.s.h.subQuot c.s.y)).Normal :=
    (LocalCores.generalized_fitting_characteristic (G := c.s.h.subQuot c.s.y)).2
  rw [c.U0_eq]
  rintro _ ⟨v, hv, rfl⟩
  obtain ⟨hvS, hvF⟩ := mem_inf.mp hv
  rw [φ_apply, c.s.t_lift, ← map_inv, ← map_mul, ← map_mul]
  exact mem_map_of_mem _ (mem_inf.mpr ⟨(mem_normalizer_iff.mp c.s.tb_norm v).mp hvS,
    (inferInstance : (generalizedFitting (c.s.h.subQuot c.s.y)).Normal).conj_mem v hvF c.s.tb⟩)

theorem secJ0_le_Lay : c.s.h.secJ0 c.s.y ≤ Seven.Lay c.s.h c.s.y :=
  Seven.J0_le_Lay c.s.h c.s.y

theorem nonempty_J_equiv :
    Nonempty (↥c.s.h.J ⧸ pPrimeCore 2 ↥c.s.h.J ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨e, -⟩ := c.s.exists_isSymSixType c.hA
  exact ⟨e⟩

theorem card_J : Nat.card (↥c.s.h.J ⧸ pPrimeCore 2 ↥c.s.h.J) = 360 := by
  obtain ⟨e⟩ := c.nonempty_J_equiv
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  decide

theorem nonempty_Lay_equiv : Nonempty (↥(Seven.Lay c.s.h c.s.y) ⧸
    pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y) ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨eJ⟩ := c.nonempty_J_equiv
  obtain ⟨e₀, -⟩ := c.s.exists_quot_equiv
  obtain ⟨eL⟩ := c.s.L_equiv
  obtain ⟨eA⟩ := c.hA
  exact nonempty_layer_equiv_alt10 c.s.h.orderOf_a
    ((c.s.h.secB0_le_secC0 c.s.y).trans inf_le_left) c.s.Lay_le_centralizer c.s.L_pc
    (c.s.G0_le_normalizer_Lay c.s.secCond.a_mem_G0) c.secJ0_le_Lay (c.s.h.secJ0_le c.s.y)
    Hyp52.isPComponent_secJ0 (e₀.trans eJ) (eL.trans eA)

theorem isRep_Lay : IsRep c.φ (Seven.Lay c.s.h c.s.y) (alternatingGroup (Fin 10)) := by
  have hLH : Seven.Lay c.s.h c.s.y ≤ c.s.h.secSub c.s.y := c.s.Lay_le_secSub
  have hθL := c.s.map_Lay_eq
  have hψmem : ∀ l : ↥(Seven.Lay c.s.h c.s.y),
      c.s.h.subQ c.s.y (inclusion hLH l) ∈ generalizedFitting (c.s.h.subQuot c.s.y) := by
    intro l
    rw [← hθL]
    exact mem_map_of_mem _ (show inclusion hLH l ∈ (Seven.Lay c.s.h c.s.y).subgroupOf
      (c.s.h.secSub c.s.y) from l.2)
  set ψ : ↥(Seven.Lay c.s.h c.s.y) →* ↥(generalizedFitting (c.s.h.subQuot c.s.y)) :=
    ((c.s.h.subQ c.s.y).comp (inclusion hLH)).codRestrict _ hψmem with hψ
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨v, hv⟩
    rw [← hθL] at hv
    obtain ⟨w, hw, rfl⟩ := mem_map.mp hv
    exact ⟨⟨w, hw⟩, Subtype.ext rfl⟩
  have h10 : Nat.factorial 10 / 2 = 1814400 := by decide
  have hcardF : Nat.card ↥(generalizedFitting (c.s.h.subQuot c.s.y)) = 1814400 := by
    obtain ⟨e⟩ := c.hA
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin, h10]
  have hle : pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y) ≤ ψ.ker := by
    have : IsSimpleGroup ↥(generalizedFitting (c.s.h.subQuot c.s.y)) := c.s.simple
    have hn : ((pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)).map ψ).Normal :=
      (inferInstance : (pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)).Normal).map _ hψsurj
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)).map ψ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      have h1 := Subgroup.card_map_dvd (H := pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)) ψ
      rw [h, card_top, hcardF] at h1
      have h2 : Odd (Nat.card (pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y))) :=
        Nat.coprime_two_left.mp pPrimeCore_coprime_card
      exact absurd (Odd.of_dvd_nat h2 h1) (by decide)
  have hker : ψ.ker = pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y) := by
    obtain ⟨eL⟩ := c.nonempty_Lay_equiv
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ψ.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ψ hψsurj).toEquiv,
      hcardF] at h1
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y))
    rw [Nat.card_congr eL.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card (α := Fin 10), Fintype.card_fin, h10] at h2
    have h3 : Nat.card ψ.ker = Nat.card (pPrimeCore 2 ↥(Seven.Lay c.s.h c.s.y)) := by omega
    exact (eq_of_le_of_card_ge hle h3.le).symm
  refine ⟨hLH, ?_, fun m hm hmN => ?_⟩
  ·
    rw [show c.φ = c.ι.comp (c.s.h.subQ c.s.y) from rfl, ← Subgroup.map_map, hθL]
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (c.ι_mem_alt v).mp hv
    · intro hu
      obtain ⟨v, rfl⟩ := c.alt_le_range hu
      exact ⟨v, (c.ι_mem_alt v).mpr hu, rfl⟩
  · have e1 : c.φ ⟨m, hmN⟩ = c.ι ((ψ ⟨m, hm⟩ : ↥(generalizedFitting (c.s.h.subQuot c.s.y))) :
        c.s.h.subQuot c.s.y) := rfl
    have e2 : c.φ ⟨m, hmN⟩ = 1 ↔ ψ ⟨m, hm⟩ = 1 := by
      rw [e1]
      constructor
      · intro h
        apply Subtype.ext
        apply c.ι_injective
        rw [h, OneMemClass.coe_one, map_one]
      · intro h
        rw [h, OneMemClass.coe_one, map_one]
    rw [e2, ← MonoidHom.mem_ker, hker]
    constructor
    · intro h
      exact mem_map_of_mem (Seven.Lay c.s.h c.s.y).subtype h
    · intro h
      obtain ⟨w, hw, hwm⟩ := mem_map.mp h
      have hwm' : w = ⟨m, hm⟩ := Subtype.ext hwm
      rwa [← hwm']

theorem map_J0 :
    ((c.s.h.secJ0 c.s.y).subgroupOf (c.s.h.secSub c.s.y)).map c.φ = altOn fixTwo := by
  rw [show c.φ = c.ι.comp (c.s.h.subQ c.s.y) from rfl, ← Subgroup.map_map, ← c.s.sec_J,
    c.map_J]

theorem Jstar0_le_Lay : conjugate (c.s.h.secJ0 c.s.y) c.s.t ≤ Seven.Lay c.s.h c.s.y := by
  intro x hx
  rw [mem_conjugate_iff] at hx
  have h := mul_mem (mul_mem (inv_mem c.htL) (c.secJ0_le_Lay hx)) c.htL
  rwa [show c.s.t⁻¹ * (c.s.t * x * c.s.t⁻¹) * c.s.t = x by group] at h

theorem map_Jstar0 : ((conjugate (c.s.h.secJ0 c.s.y) c.s.t).subgroupOf
    (c.s.h.secSub c.s.y)).map c.φ = altOn fixZ := by
  set T := c.φ ⟨c.s.t, c.s.t_H⟩ with hT
  have h1 : (conjugate (c.s.h.secJ0 c.s.y) c.s.t).subgroupOf (c.s.h.secSub c.s.y) =
      conjugate ((c.s.h.secJ0 c.s.y).subgroupOf (c.s.h.secSub c.s.y)) ⟨c.s.t, c.s.t_H⟩ := by
    ext w
    rw [mem_subgroupOf, mem_conjugate_iff, mem_conjugate_iff, mem_subgroupOf]
    rfl
  rw [h1, map_conjugate', c.map_J0, ← hT]
  have h2 : T * z0 * T⁻¹ = sigmaTwo := c.φ_t_conj.2
  have hz : T⁻¹ * sigmaTwo * T = z0 := by
    rw [← h2]
    group
  have key : ∀ i : Fin 10, T i ∈ fixTwo ↔ i ∈ fixZ := by
    intro i
    have e1 : ∀ j : Fin 10, j ∈ fixTwo ↔ sigmaTwo j = j := by decide
    have e2 : ∀ j : Fin 10, j ∈ fixZ ↔ z0 j = j := by decide
    rw [e1, e2, ← hz, Perm.mul_apply (T⁻¹ * sigmaTwo) T i, Perm.mul_apply T⁻¹ sigmaTwo (T i),
      Perm.inv_eq_iff_eq]
  ext x
  have hsign : sign (T * x * T⁻¹) = sign x := by
    rw [map_mul, map_mul, map_inv, mul_comm (sign T) (sign x), mul_assoc, mul_inv_cancel,
      mul_one]
  rw [mem_conjugate_iff, mem_altOn, mem_altOn, mem_alternatingGroup, mem_alternatingGroup, hsign,
    Perm.support_conj]
  refine and_congr Iff.rfl ⟨fun h i hi => (key i).mp (h (Finset.mem_map_of_mem _ hi)),
    fun h j hj => ?_⟩
  obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hj
  exact (key i).mpr (h hi)

theorem isPComponent_Jstar0 : conjugate (c.s.h.secJ0 c.s.y) c.s.t ≤
      centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) ∧
    IsPComponent 2 ((conjugate (c.s.h.secJ0 c.s.y) c.s.t).subgroupOf
      (centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X))) := by
  have hJ0 := Hyp52.isPComponent_secJ0 (h := c.s.h) (y := c.s.y)
  obtain ⟨hle, hpc⟩ := Six.isPComponent_conjugate (c.s.h.secJ0_le c.s.y) hJ0 c.s.t
  have htB : ∀ g, g ∈ c.s.h.secB0 c.s.y ↔ c.s.t * g * c.s.t⁻¹ ∈ c.s.h.secB0 c.s.y :=
    mem_normalizer_iff.mp c.s.t_G0
  have hta := c.toCtxA0.conj_t_a
  have heq : conjugate (centralizer ({c.s.h.a} : Set X) ⊓
      centralizer (c.s.h.secB0 c.s.y : Set X)) c.s.t =
      centralizer ({c.Z.z} : Set X) ⊓ centralizer (c.s.h.secB0 c.s.y : Set X) := by
    ext x
    rw [mem_conjugate_iff, mem_inf, mem_inf, mem_centralizer_singleton_iff,
      mem_centralizer_singleton_iff]
    have hB : c.s.t * x * c.s.t⁻¹ ∈ centralizer (c.s.h.secB0 c.s.y : Set X) ↔
        x ∈ centralizer (c.s.h.secB0 c.s.y : Set X) := by
      rw [mem_centralizer_iff, mem_centralizer_iff]
      constructor
      · intro h g hg
        have h1 := h _ ((htB g).mp hg)
        calc g * x = c.s.t⁻¹ * ((c.s.t * g * c.s.t⁻¹) * (c.s.t * x * c.s.t⁻¹)) * c.s.t := by
              group
          _ = c.s.t⁻¹ * ((c.s.t * x * c.s.t⁻¹) * (c.s.t * g * c.s.t⁻¹)) * c.s.t := by rw [h1]
          _ = x * g := by group
      · intro h g hg
        have hg' : c.s.t⁻¹ * g * c.s.t ∈ c.s.h.secB0 c.s.y := by
          rw [htB]
          rwa [show c.s.t * (c.s.t⁻¹ * g * c.s.t) * c.s.t⁻¹ = g by group]
        have h1 := h _ hg'
        calc g * (c.s.t * x * c.s.t⁻¹) = c.s.t * ((c.s.t⁻¹ * g * c.s.t) * x) * c.s.t⁻¹ := by
              group
          _ = c.s.t * (x * (c.s.t⁻¹ * g * c.s.t)) * c.s.t⁻¹ := by rw [h1]
          _ = c.s.t * x * c.s.t⁻¹ * g := by group
    rw [hB]
    refine and_congr_left fun hxB => ?_
    have hbx : x * c.b = c.b * x := (mem_centralizer_iff.mp hxB c.b c.hbB).symm
    have e1 : c.s.t * x * c.s.t⁻¹ * c.s.h.a = c.s.h.a * (c.s.t * x * c.s.t⁻¹) ↔
        x * (c.Z.z * c.b) = (c.Z.z * c.b) * x := by
      rw [← hta]
      constructor
      · intro h
        calc x * (c.s.t⁻¹ * c.s.h.a * c.s.t) =
            c.s.t⁻¹ * ((c.s.t * x * c.s.t⁻¹) * c.s.h.a) * c.s.t := by group
          _ = c.s.t⁻¹ * (c.s.h.a * (c.s.t * x * c.s.t⁻¹)) * c.s.t := by rw [h]
          _ = c.s.t⁻¹ * c.s.h.a * c.s.t * x := by group
      · intro h
        calc c.s.t * x * c.s.t⁻¹ * c.s.h.a =
            c.s.t * (x * (c.s.t⁻¹ * c.s.h.a * c.s.t)) * c.s.t⁻¹ := by group
          _ = c.s.t * ((c.s.t⁻¹ * c.s.h.a * c.s.t) * x) * c.s.t⁻¹ := by rw [h]
          _ = c.s.h.a * (c.s.t * x * c.s.t⁻¹) := by group
    rw [e1]
    constructor
    · intro h
      calc x * c.Z.z = x * (c.Z.z * c.b) * c.b := by
            rw [mul_assoc x, mul_assoc c.Z.z, c.hbb, mul_one]
        _ = c.Z.z * c.b * x * c.b := by rw [h]
        _ = c.Z.z * (c.b * x * c.b) := by group
        _ = c.Z.z * x := by rw [← hbx, mul_assoc, c.hbb, mul_one]
    · intro h
      rw [← mul_assoc, h, mul_assoc, hbx, mul_assoc]
  rw [heq] at hle hpc
  exact ⟨hle, hpc⟩

theorem φ_fix_of_mem_P {p : ↥(c.s.h.secSub c.s.y)} (hp : (p : X) ∈ c.s.h.P) :
    ∀ i ∈ fixTwo, c.φ p i = i := by
  obtain ⟨e⟩ := c.hA
  have hO := (exists_normal_form c.s.hp c.s.hp2 c.s.hf c.s.centralizer_eq e c.s.sec.orderOf_a
    c.s.sec.J_le c.s.sec.isPComponent_J c.s.J_type).1
  have hK : c.s.h.subQ c.s.y p ∈ coreActionKernel c.s.sec.J :=
    (mem_inf.mp (c.s.subQ_mem_secP hp (c.s.h.secSub_le_G0 c.s.y p.2) p.2)).2
  rw [P29.kernel_eq_centralizer hO] at hK
  apply fix_of_commute_altOn
  intro n hn
  rw [← c.map_J] at hn
  obtain ⟨j, hj, rfl⟩ := hn
  rw [φ_apply, ← map_mul, ← map_mul, (mem_centralizer_iff.mp hK j hj).symm]

theorem S_sylow : ∃ R : Sylow 2 X, (R : Subgroup X) = c.s.h.S :=
  isSylow_S_of_caseA c.s.S_sylow c.hN

theorem isSylowIn_S_centralizer_z : Seven.IsSylowIn c.s.h.S (centralizer ({c.Z.z} : Set X)) := by
  obtain ⟨R, hR⟩ := c.S_sylow
  have hSz : c.s.h.S ≤ centralizer ({c.Z.z} : Set X) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (c.Z.hzS w hw)
  refine ⟨hSz, R.subtype (hR ▸ hSz), ?_⟩
  rw [Sylow.coe_subtype, hR]

include c in
theorem kGroup_normalizer {F : Subgroup X} (hF1 : F ≠ ⊥) (hF2 : IsPGroup 2 F) :
    SectionRank.IsKGroupCat ↥(normalizer (F : Set X)) := by
  have := c.s.isSimpleGroup
  exact isKGroupCat_of_ne_top' c.s.kProper (normalizer_ne_top_of_simple c.s.nonab hF1 hF2)

include c in
theorem kGroup_centralizer {F : Subgroup X} (hF1 : F ≠ ⊥) (hF2 : IsPGroup 2 F) :
    SectionRank.IsKGroupCat ↥(centralizer (F : Set X)) := by
  have := c.s.isSimpleGroup
  refine isKGroupCat_of_ne_top' c.s.kProper fun htop =>
    normalizer_ne_top_of_simple c.s.nonab hF1 hF2 (eq_top_iff.mpr ?_)
  rw [← htop]
  exact centralizer_le_normalizer _

@[expose] noncomputable def propMCfg : PropMCfg X where
  a := c.s.h.a
  J := c.s.h.J
  B₀ := c.s.h.secB0 c.s.y
  orderOf_a := c.s.h.orderOf_a
  J_le := c.s.h.J_le
  isPComponent_J := c.s.h.isPComponent_J
  card_J := c.card_J.le
  isPGroup_B₀ := c.s.h.isPGroup_secB0 c.s.y
  B₀_le_kernel := (c.s.B0_le_P).trans inf_le_right
  B₀_le_centralizer := (c.s.h.secB0_le_secC0 c.s.y).trans inf_le_left
  J₀_le := c.secJ0_le_Lay
  equiv_L := c.nonempty_Lay_equiv
  kGroup := fun F hFB hF1 => c.kGroup_normalizer hF1 ((c.s.h.isPGroup_secB0 c.s.y).to_le hFB)

end Ctx

end CFSG.ComponentClassification.GSThmB.A10T
