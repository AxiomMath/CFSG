module

public import CFSG.CGT.Stroth77.Section44L6
public import CFSG.CGT.Stroth77.L6SylowIso
public import CFSG.CGT.Stroth77.StrothFrameD

public section

namespace CFSG.CGT.Stroth77

open CFSG.CGT.Foote81L6.Bridge
open CFSG.OddStandard.HigherRank.YamadaG23 (HasPSL6Sylow)

variable {G : Type} [Group G] [Finite G]

theorem hasPSL6Sylow_of_type201 {D : Subgroup G} {m : ℕ} (hm : 1 ≤ m)
    (e : Additive D ≃+ Torus (Type201.k m)) {c a b : D}
    (hc : e (.ofMul c) = Torus.c) (ha : e (.ofMul a) = Torus.a) (hb : e (.ofMul b) = Torus.b)
    {uv t u f : G} (huv : uv ∈ Subgroup.normalizer D) (ht : t ∈ Subgroup.normalizer D)
    (hu : u ∈ Subgroup.normalizer D)
    (huv_conj : ∀ x : D, e (.ofMul (conjBy huv x)) = (Type201.action m).φuv (e (.ofMul x)))
    (ht_conj : ∀ x : D, e (.ofMul (conjBy ht x)) = (Type201.action m).φt (e (.ofMul x)))
    (hu_conj : ∀ x : D, e (.ofMul (conjBy hu x)) = (Type201.action m).φu (e (.ofMul x)))
    (huv2 : uv * uv = 1) (ht2 : t * t = 1) (hu2 : u * u = 1) (huvt : uv * t = t * uv)
    (huvu : uv * u = u * uv) (htu : t * u = u * uv * t)
    (hf2 : f * f = 1) (hfc : f⁻¹ * c * f = (c : G)⁻¹)
    (hfa : f⁻¹ * a * f = (a : G)⁻¹ * (a : G) ^ 2 ^ (m + 1))
    (hfb : f⁻¹ * b * f = (b : G)⁻¹ * (b : G) ^ 2 ^ (m + 1))
    (hfuv : f⁻¹ * uv * f = ((c : G) * a * b) ^ 2 * uv) (hft : f⁻¹ * t * f = (a : G)⁻¹ ^ 2 * t)
    (hfu : f⁻¹ * u * f = u) (S : Sylow 2 G)
    (hS : (S : Subgroup G) = D ⊔ Subgroup.closure {uv, t, u, f}) :
    HasPSL6Sylow G := by
  set P : Subgroup G := S.toSubgroup
  have hDP : D ≤ P := hS ▸ le_sup_left
  have hmem : ∀ {x : G}, x ∈ ({uv, t, u, f} : Set G) → x ∈ P := fun hx =>
    hS ▸ le_sup_right (a := D) (Subgroup.subset_closure hx)
  let ι : D.subgroupOf P ≃* D := Subgroup.subgroupOfEquivOfLe hDP
  let e' : Additive (D.subgroupOf P) ≃+ Torus (Type201.k m) := (MulEquiv.toAdditive ι).trans e
  have hN : ∀ {g : G} (hg : g ∈ Subgroup.normalizer D) (hgP : g ∈ P),
      (⟨g, hgP⟩ : P) ∈ Subgroup.normalizer (D.subgroupOf P) :=
    fun hg _ => Subgroup.le_normalizer_comap P.subtype hg
  have he' : ∀ y : D, e' (.ofMul (ι.symm y)) = e (.ofMul y) := fun y => by
    simp [e']
  have huvP : uv ∈ P := hmem (by simp)
  have htP : t ∈ P := hmem (by simp)
  have huP : u ∈ P := hmem (by simp)
  have hfP : f ∈ P := hmem (by simp)
  have hgen : D.subgroupOf P ⊔ Subgroup.closure
      {(⟨uv, huvP⟩ : P), ⟨t, htP⟩, ⟨u, huP⟩, ⟨f, hfP⟩} = ⊤ := by
    apply Subgroup.map_injective P.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hDP, MonoidHom.map_closure,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    simp only [Set.image_insert_eq, Set.image_singleton, Subgroup.coe_subtype]
    exact hS.symm
  obtain ⟨eP⟩ := nonempty_mulEquiv_sModel_of_type201 hm e' (c := ι.symm c) (a := ι.symm a)
    (b := ι.symm b) ((he' c).trans hc) ((he' a).trans ha) ((he' b).trans hb)
    (hN huv huvP) (hN ht htP) (hN hu huP) (fun x => huv_conj (ι x)) (fun x => ht_conj (ι x))
    (fun x => hu_conj (ι x)) (Subtype.ext huv2) (Subtype.ext ht2) (Subtype.ext hu2)
    (Subtype.ext huvt) (Subtype.ext huvu) (Subtype.ext htu) (Subtype.ext hf2) (Subtype.ext hfc)
    (Subtype.ext hfa) (Subtype.ext hfb) (Subtype.ext hfuv) (Subtype.ext hft) (Subtype.ext hfu)
    hgen
  exact hasPSL6Sylow_of_mulEquiv_sModel S hm eP

theorem StrothFrame.IsD.hasPSL6Sylow_of_stroth44 {F : StrothFrame G} {D : Subgroup G} {m : ℕ}
    {dD : StrothWeakTypeData D (.t201 m)} (h : F.IsD D dD) {e : G}
    (hec : e⁻¹ * (dD.c : G) * e = (dD.c : G)⁻¹)
    (hea : e⁻¹ * (dD.a : G) * e = (dD.a : G)⁻¹ * (dD.a : G) ^ 2 ^ (m + 1))
    (heb : e⁻¹ * (dD.b : G) * e = (dD.b : G)⁻¹ * (dD.b : G) ^ 2 ^ (m + 1))
    (he2 : e * e = 1) (heuv : e⁻¹ * dD.uv * e = dD.cab ^ 2 * dD.uv)
    (het : e⁻¹ * dD.t * e = (dD.a : G)⁻¹ ^ 2 * dD.t) (heu : e⁻¹ * dD.u * e = dD.u)
    (hS : (F.S : Subgroup G) = D ⊔ Subgroup.closure {F.dA.uv, F.dA.t, F.dA.u, e}) :
    HasPSL6Sylow G := by
  have hm : 1 ≤ m := by
    have h1 := Subgroup.card_le_of_le h.A_le
    rw [F.dA.card, dD.card] at h1
    have h2 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h1
    simp only [StrothTypeIndex.k, Type100.k, Type201.k, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h2
    omega
  rw [← h.uv_eq, ← h.t_eq, ← h.u_eq] at hS
  exact hasPSL6Sylow_of_type201 hm dD.e (c := dD.c) (a := dD.a) (b := dD.b)
    (dD.e.apply_symm_apply _) (dD.e.apply_symm_apply _) (dD.e.apply_symm_apply _)
    dD.uv_mem dD.t_mem dD.u_mem dD.uv_conj dD.t_conj dD.u_conj dD.uv_sq dD.t_sq dD.u_sq
    dD.uv_comm_t dD.uv_comm_u dD.t_u he2 hec hea heb heuv het heu F.S hS

end CFSG.CGT.Stroth77
