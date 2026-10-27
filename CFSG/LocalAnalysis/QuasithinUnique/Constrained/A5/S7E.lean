module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7A
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.S7Fin

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split

theorem isEven_rmul {a b : RP} (ha : isEven a.1) (hb : isEven b.1) : isEven (rmul a b).1 :=
  (mem_evenWeight_iff _).mp ((evenWeight 5).add_mem ((mem_evenWeight_iff _).mpr ha)
    (pact_mem _ ((mem_evenWeight_iff _).mpr hb)))

namespace Sec

variable {G : Type} [Group G] [Finite G] {T M H S L : Subgroup G} {C : StdCfg T M H S L}
  (X : Sec C)

include X

@[expose] noncomputable def embR (r : RP) (hr : isEven r.1) : ↥H := X.emb ⟨r.1, hr⟩ r.2

theorem embR_congr {r r' : RP} (h : r = r') (hr : isEven r.1) (hr' : isEven r'.1) :
    X.embR r hr = X.embR r' hr' := by
  subst h
  rfl

theorem embR_mul {a b : RP} (ha : isEven a.1) (hb : isEven b.1) :
    X.embR a ha * X.embR b hb = X.embR (rmul a b) (isEven_rmul ha hb) := by
  unfold embR
  rw [X.emb_mul]
  exact X.emb_congr (Subtype.ext rfl) rfl

theorem embR_rone : X.embR rone (by decide +kernel) = 1 := by
  rw [← X.emb_zero_one]
  exact X.emb_congr (Subtype.ext rfl) rfl

theorem pi_embR (r : RP) (hr : isEven r.1) : C.D.π (X.embR r hr) = r.2 := X.pi_emb _ _

@[expose] noncomputable def rhom {Γ : Type*} [Group Γ] (tab : Γ → RP)
    (hev : ∀ x, isEven (tab x).1) (h1 : tab 1 = rone)
    (hmul : ∀ x y, rmul (tab x) (tab y) = tab (x * y)) : Γ →* ↥H where
  toFun g := X.embR (tab g) (hev g)
  map_one' := by
    show X.embR (tab 1) (hev 1) = 1
    rw [← X.embR_rone]
    exact X.embR_congr h1 _ _
  map_mul' x y := by
    show X.embR (tab (x * y)) (hev _) = X.embR (tab x) (hev x) * X.embR (tab y) (hev y)
    rw [X.embR_mul (hev x) (hev y)]
    exact X.embR_congr (hmul x y).symm _ _

@[expose] noncomputable def huHom
    : DihedralGroup 4 × Equiv.Perm (Fin 4) →* ↥H :=
  MonoidHom.noncommCoprod
    (X.rhom dtab (fun x => (dtab_fix x).2) dtab_one dmul)
    (X.rhom ptab (fun x => (ptab_fix x).2) ptab_one pmul)
    (fun d s => by
      show X.embR (dtab d) _ * X.embR (ptab s) _ = X.embR (ptab s) _ * X.embR (dtab d) _
      rw [X.embR_mul, X.embR_mul]
      exact X.embR_congr (dpcomm d s) _ _)

theorem huHom_apply (x : DihedralGroup 4 × Equiv.Perm (Fin 4)) :
    X.huHom x = X.embR (rmul (dtab x.1) (ptab x.2))
      (isEven_rmul (dtab_fix x.1).2 (ptab_fix x.2).2) := by
  show X.embR (dtab x.1) _ * X.embR (ptab x.2) _ = _
  exact X.embR_mul _ _

theorem huHom_inj : Function.Injective X.huHom := by
  rw [injective_iff_map_eq_one]
  rintro ⟨d, s⟩ h
  rw [X.huHom_apply] at h
  have h0 : X.embR (rmul (dtab d) (ptab s)) (isEven_rmul (dtab_fix d).2 (ptab_fix s).2) =
      X.embR rone (by decide +kernel) := h.trans X.embR_rone.symm
  obtain ⟨h1, h2⟩ := X.emb_inj h0
  have hr : rmul (dtab d) (ptab s) = rone :=
    Prod.ext (congrArg Subtype.val h1) h2
  obtain ⟨hd, hs⟩ := dp_kernel d s hr
  rw [hd, hs]
  rfl

theorem pi_huHom (x : DihedralGroup 4 × Equiv.Perm (Fin 4)) :
    C.D.π (X.huHom x) = (dtab x.1).2 * (ptab x.2).2 := by
  rw [X.huHom_apply, X.pi_embR]
  rfl

theorem huHom_mem_cent (x : DihedralGroup 4 × Equiv.Perm (Fin 4)) :
    ((X.huHom x : ↥H) : G) ∈ centralizerElem C.u0 := by
  rw [X.mem_cent_iff, X.pi_huHom]
  apply Subtype.ext
  show pact ((dtab x.1).2 * (ptab x.2).2) g1 = g1
  rw [pact_mul, (ptab_fix x.2).1, (dtab_fix x.1).1]

theorem huHom_surj {h : ↥H} (hh : (h : G) ∈ centralizerElem C.u0) :
    ∃ x, X.huHom x = h := by
  have hfix : vact (C.D.π h) g1w = g1w := (X.mem_cent_iff h).mp hh
  have hσ : pact (C.D.π h) g1 = g1 := congrArg Subtype.val hfix
  obtain ⟨d, s, hds⟩ := dp_cover (X.cw h).1 (X.cw h).2 (C.D.π h) hσ
  refine ⟨(d, s), ?_⟩
  rw [X.huHom_apply]
  have : X.embR (rmul (dtab d) (ptab s)) (isEven_rmul (dtab_fix d).2 (ptab_fix s).2) =
      X.embR ((X.cw h).1, C.D.π h) (X.cw h).2 := X.embR_congr hds _ _
  rw [this]
  exact (X.cw_spec h).symm

theorem Hu_iso :
    Nonempty (↥(H ⊓ centralizerElem C.u0) ≃* DihedralGroup 4 × Equiv.Perm (Fin 4)) := by
  have hmem : ∀ x, X.huHom x ∈ (H ⊓ centralizerElem C.u0).subgroupOf H := fun x =>
    Subgroup.mem_subgroupOf.mpr ⟨(X.huHom x).2, X.huHom_mem_cent x⟩
  let Φ' : DihedralGroup 4 × Equiv.Perm (Fin 4) →* ↥(H ⊓ centralizerElem C.u0) :=
    (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ centralizerElem C.u0 ≤ H)).toMonoidHom.comp
      (X.huHom.codRestrict _ hmem)
  have hbij : Function.Bijective Φ' := by
    constructor
    · intro x y hxy
      apply X.huHom_inj
      have := congrArg (fun z : ↥(H ⊓ centralizerElem C.u0) => (z : G)) hxy
      exact Subtype.ext this
    · intro y
      obtain ⟨x, hx⟩ := X.huHom_surj (h := ⟨(y : G), y.2.1⟩) y.2.2
      refine ⟨x, ?_⟩
      apply Subtype.ext
      exact congrArg (fun z : ↥H => (z : G)) hx
  exact ⟨(MulEquiv.ofBijective Φ' hbij).symm⟩

end Sec

end CFSG.QuasithinUnique.A5
