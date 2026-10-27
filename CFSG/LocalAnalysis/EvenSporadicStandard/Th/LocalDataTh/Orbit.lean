module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.DataLemmas
public import CFSG.Sporadic.ThSchreier.BFS
public import Certificates.Certificate24201

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3 CFSG.Sporadic.LySchreier CFSG.Sporadic.ThSchreier
open scoped Matrix

theorem B1c_lt : ∀ x ∈ B1c, x < 256 := by decide

theorem B2c_lt : ∀ x ∈ B2c, x < 256 := by decide

section Gen

variable {G Y : Type*} [Group G] [MulAction G Y] [DecidableEq Y]

theorem mem_bfsList_iff_mem_orbit {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (fa fb : Y → Y) (hfa : ∀ y, a • y = fa y) (hfb : ∀ y, b • y = fb y) (y₀ : Y) {N : ℕ}
    (hN : (bfsList [fa, fb] y₀ N).length ≤ N) (y : Y) :
    y ∈ bfsList [fa, fb] y₀ N ↔ y ∈ MulAction.orbit G y₀ := by
  constructor
  · refine bfsList_mem_of_closed [fa, fb] y₀ (MulAction.mem_orbit_self y₀) ?_ N y
    intro g hg x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · rw [← hfa]; exact MulAction.mem_orbit_of_mem_orbit a hx
    · rw [← hfb]; exact MulAction.mem_orbit_of_mem_orbit b hx
  · rintro ⟨g, rfl⟩
    have hS : {y | y ∈ bfsList [fa, fb] y₀ N}.Finite := (bfsList [fa, fb] y₀ N).finite_toSet
    refine smul_mem_of_closure hgen hS ?_ ?_ g y₀ (root_mem_bfsList [fa, fb] y₀ N)
    · intro y hy
      rw [hfa]
      exact bfsList_closed [fa, fb] y₀ hN (by simp) hy
    · intro y hy
      rw [hfb]
      exact bfsList_closed [fa, fb] y₀ hN (by simp) hy

theorem card_orbit_of_bfsList {a b : G} (hgen : Subgroup.closure ({a, b} : Set G) = ⊤)
    (fa fb : Y → Y) (hfa : ∀ y, a • y = fa y) (hfb : ∀ y, b • y = fb y) (y₀ : Y) {N : ℕ}
    {L : List Y} (hL : L = bfsList [fa, fb] y₀ N) (hN : L.length ≤ N) :
    Nat.card (MulAction.orbit G y₀) = L.length := by
  subst hL
  have e : MulAction.orbit G y₀ = ↑((bfsList [fa, fb] y₀ N).toFinset) := by
    ext y
    rw [← mem_bfsList_iff_mem_orbit hgen fa fb hfa hfb y₀ hN y]
    simp
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset,
    List.toFinset_card_of_nodup (bfsList_nodup [fa, fb] y₀ N)]

end Gen

section Act


@[expose] def decV (c : Fin 256) : Vec := codeVec 8 c.val

@[expose] noncomputable def encV (v : Vec) : Fin 256 :=
  ⟨Classical.choose (exists_codeVec 8 v), by
    have := (Classical.choose_spec (exists_codeVec 8 v)).1
    simpa using this⟩

theorem decV_encV (v : Vec) : decV (encV v) = v := (Classical.choose_spec (exists_codeVec 8 v)).2

theorem encV_decV (c : Fin 256) : encV (decV c) = c := by
  apply Fin.ext
  exact codeVec_inj_of_lt (encV (decV c)).2 c.2 (decV_encV (decV c))

theorem encV_codeVec {d : ℕ} (hd : d < 256) : encV (codeVec 8 d) = Fin.ofNat 256 d := by
  apply Fin.ext
  rw [Fin.val_ofNat, Nat.mod_eq_of_lt hd]
  exact codeVec_inj_of_lt (encV (codeVec 8 d)).2 hd (decV_encV (codeVec 8 d))

noncomputable instance instMulActionFin : MulAction ↥M (Fin 256) where
  smul m c := encV (rho (m : J) *ᵥ decV c)
  one_smul c := by
    show encV (rho ((1 : ↥M) : J) *ᵥ decV c) = c
    rw [Subgroup.coe_one, rho_one, Matrix.one_mulVec, encV_decV]
  mul_smul a b c := by
    show encV (rho ((a * b : ↥M) : J) *ᵥ decV c) =
      encV (rho (a : J) *ᵥ decV (encV (rho (b : J) *ᵥ decV c)))
    rw [decV_encV, Matrix.mulVec_mulVec, Subgroup.coe_mul, rho_mul a.2 b.2]

theorem smul_fin_def (m : ↥M) (c : Fin 256) : m • c = encV (rho (m : J) *ᵥ decV c) := rfl

theorem imgTab_getD (cs : List ℕ) (c : Fin 256) :
    (imgTab cs).getD c.val 0 = applyCols 8 cs c.val := by
  simp [imgTab, List.getD_eq_getElem?_getD, c.2]

theorem smul_gen (cs : List ℕ) (hcs : ∀ x ∈ cs, x < 256) {g : ↥M}
    (hg : rho (g : J) = matOfCols 8 cs) (c : Fin 256) : g • c = imgFin (imgTab cs) c := by
  rw [smul_fin_def, hg, decV, matOfCols_mulVec, encV_codeVec (applyCols_lt hcs c.val), imgFin,
    imgTab_getD]

theorem smul_eq_iff (m : ↥M) (c : Fin 256) : m • c = c ↔ rho (m : J) *ᵥ decV c = decV c := by
  rw [smul_fin_def]
  constructor
  · intro h
    have := congrArg decV h
    rwa [decV_encV] at this
  · intro h
    rw [h, encV_decV]

end Act

section Count


@[expose] noncomputable def gx : ↥M := ⟨x, x_mem_M⟩

@[expose] noncomputable def gy : ↥M := ⟨y, y_mem_M⟩

theorem rho_gx : rho (gx : J) = matOfCols 8 B1c := by
  rw [show (gx : J) = x from rfl, rho_x, B1_eq]

theorem rho_gy : rho (gy : J) = matOfCols 8 B2c := by
  rw [show (gy : J) = y from rfl, rho_y, B2_eq]

theorem smul_gx_Y3 (t : Y3) : gx • t = mapX t :=
  Prod.ext (smul_gen B1c B1c_lt rho_gx _)
    (Prod.ext (smul_gen B1c B1c_lt rho_gx _) (smul_gen B1c B1c_lt rho_gx _))

theorem smul_gy_Y3 (t : Y3) : gy • t = mapY t :=
  Prod.ext (smul_gen B2c B2c_lt rho_gy _)
    (Prod.ext (smul_gen B2c B2c_lt rho_gy _) (smul_gen B2c B2c_lt rho_gy _))

theorem closure_gx_gy : Subgroup.closure ({gx, gy} : Set ↥M) = ⊤ := by
  have h1 : (Subgroup.closure ({gx, gy} : Set ↥M)).map M.subtype = M := by
    rw [MonoidHom.map_closure, Set.image_pair]
    rfl
  have h2 : (⊤ : Subgroup ↥M).map M.subtype = M := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact Subgroup.map_injective M.subtype_injective (h1.trans h2.symm)

theorem orbitList_def : orbitList = bfsList [mapX, mapY] rootY3 22680 := rfl


theorem card_orbit_rootY3 : Nat.card (MulAction.orbit ↥M rootY3) = 22680 := by
  have hlen := Certificates.certificate24201
  rw [card_orbit_of_bfsList closure_gx_gy mapX mapY smul_gx_Y3 smul_gy_Y3 rootY3 orbitList_def
    hlen.le, hlen]

theorem card_stabilizer_rootY3 : Nat.card (MulAction.stabilizer ↥M rootY3) = 4096 := by
  have h := (MulAction.stabilizer ↥M rootY3).card_mul_index
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq, card_orbit_rootY3, card_M] at h
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) (h.trans (by norm_num))

end Count

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
