module

public import Certificates.Certificate13621
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22WitnessBase1
public import CFSG.Sporadic.FischerOddCore.RefineSpec

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three

open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Perm CFSG.Perm.Native CFSG.Sporadic.Fi22.S0 CFSG.HardMathSupport.Foote.E27
  CFSG.HardMathSupport.Foote.E27.Fi22S0 CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Native
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FiNative CFSG.Sporadic.FischerOddCore
  CFSG.Sporadic.FischerOddCore.Native CFSG.Certificates CFSG.Certificates.Native


theorem compT_size (P Q : Table) : (compT 3510 P Q).size = 3510 := by
  unfold compT; simp

theorem idT_size : (idT 3510).size = 3510 := by unfold idT; simp

theorem eltT_size (P : Array (ℕ × ℕ)) (G : Array Table) (i : ℕ) : (eltT P G i).size = 3510 := by
  rw [eltT.eq_def]
  split_ifs
  · exact compT_size _ _
  · exact idT_size

theorem rep_natOf {X : Table} {g : J} (hX : Rep 3510 X g) (hs : X.size = 3510) :
    CFSG.Monster.B.Co2.Rep 3510 (natOf X) (MulAction.toPerm g) := by
  intro v
  unfold natOf
  rw [getElem!_pos _ (v : ℕ) (by simp [hs]), Array.getElem_map]
  have h := hX v.val v.2
  unfold ap at h
  rw [getElem!_pos X (v : ℕ) (by rw [hs]; exact v.2)] at h
  rw [h, idx_of_lt g v.2]
  rfl

theorem transT_get {k : ℕ} (hk : k < 3510) :
    (transT orb)[k]! = cTab orb (genTables orb (-2)) k := by
  unfold transT
  simp only
  exact getElem!_ofFn_any _ hk

theorem rep_transT {k : ℕ} (hk : k < 3510) : Rep 3510 (transT orb)[k]! (conjPt k) := by
  rw [transT_get hk]
  exact rep_cTab k hk

theorem idx_conjPt_eq_iff {x y : ℕ} (hy : y < 3510) :
    idx 3510 (conjPt x) y = y ↔ conjPt x * conjPt y = conjPt y * conjPt x := by
  rw [idx_eq_iff hy hy]
  constructor
  · intro h
    calc conjPt x * conjPt y = conjPt x * conjPt y * (conjPt x)⁻¹ * conjPt x := by group
      _ = conjPt y * conjPt x := by rw [h]
  · intro h
    rw [h, mul_inv_cancel_right]

theorem nbrJ_get (D : Array Table) {v : ℕ} (hv : v < 3510) :
    (nbrJ D)[v]! = (List.range 3510).filter fun w => w != v && ap D[v]! w == w := by
  unfold nbrJ
  rw [getElem!_ofFn_any _ hv]
  rfl

theorem pointList_nbrJ (D : Array Table) (x : Fin 3510) :
    CFSG.Certificates.PointList 3510 (nbrJ D)[(x : ℕ)]! := by
  rw [nbrJ_get D x.2]
  refine ⟨fun q hq => ?_, ?_⟩
  · exact List.mem_range.1 (List.mem_of_mem_filter hq)
  · exact (List.pairwise_lt_range).filter _

theorem mem_nbrJ {x y : Fin 3510} :
    (y : ℕ) ∈ (nbrJ (transT orb))[(x : ℕ)]! ↔ y ≠ x ∧ x.val ≠ y.val ∧
      conjPt x * conjPt y = conjPt y * conjPt x := by
  rw [nbrJ_get _ x.2, List.mem_filter]
  simp only [List.mem_range, Bool.and_eq_true, bne_iff_ne, beq_iff_eq]
  rw [rep_transT x.2 y.val y.2, idx_conjPt_eq_iff y.2]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun e => h1 (congrArg Fin.val e), fun e => h1 e.symm, h2⟩
  · rintro ⟨h1, -, h2⟩
    exact ⟨y.2, fun e => h1 (Fin.ext e), h2⟩

theorem nbrInv_toPerm (g : J) :
    CFSG.Certificates.NbrInv (nbrJ (transT orb)) (MulAction.toPerm g : Equiv.Perm (Fin 3510)) := by
  intro x y
  simp only [MulAction.toPerm_apply]
  rw [mem_nbrJ, mem_nbrJ]
  have hx := conjPt_smul g x
  have hy := conjPt_smul g y
  rw [hx, hy]
  constructor
  · rintro ⟨h1, -, h2⟩
    refine ⟨fun e => h1 (smul_left_cancel g e), fun e => h1 (smul_left_cancel g (Fin.ext e).symm),
      ?_⟩
    calc g * conjPt x * g⁻¹ * (g * conjPt y * g⁻¹) = g * (conjPt x * conjPt y) * g⁻¹ := by group
      _ = g * (conjPt y * conjPt x) * g⁻¹ := by rw [h2]
      _ = g * conjPt y * g⁻¹ * (g * conjPt x * g⁻¹) := by group
  · rintro ⟨h1, -, h2⟩
    refine ⟨fun e => h1 (by rw [e]), fun e => h1 (by rw [Fin.ext e]), ?_⟩
    have h3 : g * (conjPt x * conjPt y) * g⁻¹ = g * (conjPt y * conjPt x) * g⁻¹ := by
      calc g * (conjPt x * conjPt y) * g⁻¹ = g * conjPt x * g⁻¹ * (g * conjPt y * g⁻¹) := by
            group
        _ = g * conjPt y * g⁻¹ * (g * conjPt x * g⁻¹) := h2
        _ = g * (conjPt y * conjPt x) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h3)

theorem countP_range_eq_card (q : ℕ → Bool) :
    (List.range 3510).countP q = Nat.card {w : Fin 3510 // q w = true} :=
  (card_fin_subtype_eq_countP 3510 q).symm

theorem c0J_get {X : Table} {v : ℕ} (hv : v < 3510) :
    (c0J (transT orb) X)[v]! =
      (List.range 3510).countP fun w => ap (compT 3510 (transT orb)[v]! X) w == w := by
  unfold c0J
  rw [getElem!_ofFn_any _ hv]
  rfl

theorem c0J_eq {X : Table} {x : J} (hX : Rep 3510 X x) (v : Fin 3510) :
    (c0J (transT orb) X)[(v : ℕ)]! = Nat.card {w : Fin 3510 // (conjPt v * x) • w = w} := by
  rw [c0J_get v.2, countP_range_eq_card]
  have hr := (rep_transT v.2).compT hX
  refine Nat.card_congr (Equiv.subtypeEquivRight fun w => ?_)
  rw [beq_iff_eq, hr w.val w.2, idx_of_lt _ w.2]
  exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩

theorem card_fix_conj (g y : J) :
    Nat.card {w : Fin 3510 // (g * y * g⁻¹) • w = w} = Nat.card {w : Fin 3510 // y • w = w} := by
  refine Nat.card_congr
    { toFun := fun w => ⟨g⁻¹ • w.1, ?_⟩
      invFun := fun w => ⟨g • w.1, ?_⟩
      left_inv := fun w => Subtype.ext (smul_inv_smul g w.1)
      right_inv := fun w => Subtype.ext (inv_smul_smul g w.1) }
  · have h := w.2
    rw [mul_smul, mul_smul] at h
    calc y • g⁻¹ • w.1 = g⁻¹ • (g • y • g⁻¹ • w.1) := by rw [inv_smul_smul]
      _ = g⁻¹ • w.1 := by rw [h]
  · have h := w.2
    rw [mul_smul, mul_smul, inv_smul_smul, h]

theorem colMap_c0J {X : Table} {x g : J} (hX : Rep 3510 X x) (hg : g * x = x * g) :
    ColMap 3510 (c0J (transT orb) X) (c0J (transT orb) X)
      (MulAction.toPerm g : Equiv.Perm (Fin 3510)) := by
  intro v
  simp only [MulAction.toPerm_apply]
  rw [c0J_eq hX, c0J_eq hX, conjPt_smul]
  have e : g * conjPt v * g⁻¹ * x = g * (conjPt v * x) * g⁻¹ := by
    have : x = g * x * g⁻¹ := by rw [hg, mul_inv_cancel_right]
    calc g * conjPt v * g⁻¹ * x = g * conjPt v * g⁻¹ * (g * x * g⁻¹) := by rw [← this]
      _ = g * (conjPt v * x) * g⁻¹ := by group
  rw [e, card_fix_conj]

theorem toPerm_comm {x g : J} (hg : g * x = x * g) :
    (MulAction.toPerm g : Equiv.Perm (Fin 3510)) * MulAction.toPerm x =
      MulAction.toPerm x * MulAction.toPerm g := by
  ext v
  simp only [Equiv.Perm.mul_apply, MulAction.toPerm_apply]
  rw [← mul_smul, hg, mul_smul]

theorem conj_eq_self_iff {g c : J} : g * c * g⁻¹ = c ↔ c * g = g * c := by
  rw [mul_inv_eq_iff_eq_mul]
  exact eq_comm

theorem mem_fixList {X : Table} {x : J} (hX : Rep 3510 X x) (v : Fin 3510) :
    (v : ℕ) ∈ fixList X ↔ x • v = v := by
  unfold fixList
  rw [List.mem_filter, List.mem_range, beq_iff_eq, hX v.val v.2, idx_of_lt x v.2]
  exact ⟨fun h => Fin.ext h.2, fun h => ⟨v.2, congrArg Fin.val h⟩⟩

theorem lt_of_mem_fixList {X : Table} {v : ℕ} (hv : v ∈ fixList X) : v < 3510 := by
  unfold fixList at hv
  rw [List.mem_filter, List.mem_range] at hv
  exact hv.1

theorem map_fixList {X : Table} {x : J} (hX : Rep 3510 X x) {σ : Equiv.Perm (Fin 3510)}
    (hσ : ∀ v : Fin 3510, x • v = v → σ v = v) : (fixList X).map (permNat σ) = fixList X := by
  conv_rhs => rw [← List.map_id (fixList X)]
  refine List.map_congr_left fun v hv => ?_
  have hvn := lt_of_mem_fixList hv
  rw [permNat_lt σ hvn, hσ _ ((mem_fixList hX ⟨v, hvn⟩).1 hv)]
  rfl

theorem rep_xRep (k : ℕ) (hk : k < 4) :
    Rep 3510 (eltT par (genT orb) globRep[k]!) (xRep k) := by
  rw [xRep_def]
  exact rep_eltT _ (globRep_lt k hk)

theorem xRep_zero_smul_ne
    (v : Fin 3510) : xRep 0 • v ≠ v :=
  Certificates.certificate13621.1 v

theorem eq_one_of_idOK {T : Table} {g : J} (hT : Rep 3510 T g) (h : idOK T = true) : g = 1 := by
  apply eq_one_of_fix_all
  intro i
  have h1 := allIn_eq_true.1 h i.val (Nat.zero_le _) i.2
  rw [beq_iff_eq, hT i.val i.2, idx_of_lt g i.2] at h1
  exact Fin.ext h1

theorem idOK_of_eq_one {T : Table} {g : J} (hT : Rep 3510 T g) (h : g = 1) : idOK T = true := by
  unfold idOK
  rw [allIn_eq_true]
  intro i _ hi
  rw [beq_iff_eq, hT i hi, h, idx_one]

theorem exists_orderOf_four_comm :
    ∃ t : J, orderOf t = 4 ∧ t * xRep 0 = xRep 0 * t :=
  Certificates.certificate13621.2.1

theorem card_map_toPerm (H : Subgroup J) :
    Nat.card (H.map (MulAction.toPermHom J (Fin 3510))) = Nat.card H := by
  have hinj : Function.Injective (MulAction.toPermHom J (Fin 3510)) := by
    intro g h e
    apply eq_of_smul_eq_smul (α := Fin 3510)
    intro i
    exact congrArg (fun σ : Equiv.Perm (Fin 3510) => σ i) e
  exact Subgroup.card_map_of_injective hinj

theorem fpfBounds_prod : fpfBounds.prod = 34992 := by decide

theorem card_centralizer_xRep_zero_le :
    Nat.card (Subgroup.centralizer ({xRep 0} : Set J)) ≤ 34992 :=
  Certificates.certificate13621.2.2.1

@[expose] def fixStab (x : J) : Subgroup J where
  carrier := {g | ∀ v : Fin 3510, x • v = v → g • v = v}
  mul_mem' := fun {g h} hg hh v hv => by rw [mul_smul, hh v hv, hg v hv]
  one_mem' := fun v _ => one_smul J v
  inv_mem' := fun {g} hg v hv => by
    have := hg v hv
    rw [← this, inv_smul_smul, this]

theorem fixExtra_lt : ∀ k < 4, fixExtra[k]! < 3510 := by decide

theorem card_centralizer_fix_le
    {k : ℕ} (hk : k ∈ [1, 2, 3]) :
    Nat.card ↥(Subgroup.centralizer ({xRep k} : Set J) ⊓ fixStab (xRep k)) ≤ 3 := by
  have e : Nat.card ↥(Subgroup.centralizer ({xRep k} : Set J) ⊓ fixStab (xRep k)) =
      Nat.card {g : J // g ∈ Subgroup.centralizer ({xRep k} : Set J) ∧
        ∀ v : Fin 3510, xRep k • v = v → g • v = v} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
  rw [e]
  exact Certificates.certificate13621.2.2.2.1 k hk

theorem sep_xRep {k : ℕ}
    (hk : k ∈ [1, 2, 3]) :
    ∀ d ∈ D, d * xRep k = xRep k * d → ∀ d' ∈ D, d' * xRep k = xRep k * d' → d ≠ d' →
      d * d' = d' * d → ∃ e ∈ D, e * xRep k = xRep k * e ∧ e * d' = d' * e ∧ e * d ≠ d * e :=
  Certificates.certificate13621.2.2.2.2 k hk

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi22Three
