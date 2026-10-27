module

public import CFSG.LieType.SpecialLinear.CurtisDatum.NegExcept
public import CFSG.LieType.SpecialLinear.CurtisDatum.Torus
public import CFSG.LieType.SpecialLinear.CurtisDatum.RankOne
public import CFSG.LieType.SpecialLinear.CurtisDatum.Unipotent
public import CFSG.LieType.SpecialLinear.CurtisDatum.Cover
public import CFSG.LieType.SpecialLinear.CurtisDatum.Hecke
public import CFSG.Quasithin.Background.SmithCurtisDatum
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw.CoverType

public section

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fact (Nat.Prime p)] in
theorem isPGroup_rootGroup_charP {γ : Fin m → ℤ} (hγ : γ ∈ (rootDatum m F).roots) :
    IsPGroup p ((rootDatum m F).rootGroup γ) := by
  change IsPGroup p (rootGroup m F γ)
  rw [rootGroup_eq_idx m F hγ]
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp, hn⟩ := FiniteField.card F p
  have hn' : Nat.card F = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]
    exact hn
  let f := SpecialLinearGroup.transvectionHom (A := F) (idx_spec m hγ).1
  have hinj : Function.Injective f := by
    intro a b h
    have h' : SpecialLinearGroup.transvection (idx_spec m hγ).1 (Multiplicative.toAdd a) =
        SpecialLinearGroup.transvection (idx_spec m hγ).1 (Multiplicative.toAdd b) := by
      simpa [f] using h
    exact Multiplicative.toAdd.injective
      (SpecialLinearGroup.transvection_injective (A := F) (idx_spec m hγ).1 h')
  have hcard : Nat.card (rootSubgroup m F (idx_spec m hγ).1) = p ^ (n : ℕ) := by
    rw [show rootSubgroup m F (idx_spec m hγ).1 = f.range from rfl]
    have hrange : Nat.card (↥f.range) = Nat.card (Multiplicative F) :=
      Nat.card_congr ((Equiv.Set.congr (MonoidHom.coe_range f)).trans
        (Equiv.ofInjective f hinj).symm)
    rw [hrange, show Nat.card (Multiplicative F) = Nat.card F from
      Nat.card_congr Multiplicative.ofAdd, hn']
  exact IsPGroup.of_card hcard

omit [Finite F] in
theorem rootGroup_single_ne_bot (k : Fin m) :
    rootGroup m F (Pi.single k 1) ≠ ⊥ := by
  intro hbot
  have hmem : SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (1 : F) ∈
      rootGroup m F (Pi.single k 1) := by
    rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne) (by rw [toStd_single])]
    exact transvection_mem_rootSubgroup (m := m) (F := F)
      (hij := (Fin.castSucc_lt_succ (i := k)).ne) (c := 1)
  rw [hbot] at hmem
  have hne : SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (1 : F) ≠ 1 := by
    intro h
    have hmat : ((SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) (1 : F) :
        Matrix.SpecialLinearGroup (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F) =
        ((1 : Matrix.SpecialLinearGroup (Fin (m+1)) F) : Matrix (Fin (m+1)) (Fin (m+1)) F) :=
      congrArg Subtype.val h
    have h2 := congrFun (congrFun hmat k.castSucc) k.succ
    simp only [Matrix.SpecialLinearGroup.coe_one, Matrix.one_apply, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.add_apply, Matrix.single_apply] at h2
    rw [if_neg (Fin.castSucc_lt_succ (i := k)).ne] at h2
    norm_num at h2
  exact hne (Subgroup.mem_bot.mp hmem)

omit [Fact (Nat.Prime p)] in
theorem isPElt_of_mem_rootGroup_charP {γ : Fin m → ℤ} (hγ : γ ∈ (rootDatum m F).roots)
    {x : Matrix.SpecialLinearGroup (Fin (m + 1)) F} (hx : x ∈ rootGroup m F γ) :
    IsPElt p x := by
  change ∃ k, x ^ (p ^ k) = 1
  have hP := isPGroup_rootGroup_charP m F p hγ
  obtain ⟨k, hk⟩ := (isPGroup_iff_pow_pow_eq_one.mp hP) ⟨x, hx⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩


abbrev curtisCoxeterSystem : CoxeterSystem (coxeterMatrix (isFiniteType_A m))
    (coxeterMatrix (isFiniteType_A m)).Group :=
  (CFSG.LieType.RootSystem.coxeterMatrix (isFiniteType_A m)).toCoxeterSystem

omit [Finite F] in
theorem U_eq_aux (s : Fin m) (u : Matrix.SpecialLinearGroup (Fin (m + 1)) F)
    (hu : u ∈ posUnipotent (rootDatum m F)) :
    ∃ x ∈ rootGroup m F (Pi.single s 1),
      ∃ v ∈ posUnipotentExcept (rootDatum m F) s, u = x * v := by
  have hpos := posUnipotent_eq_sup (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
    (steinbergExtras m F) s
  rw [hpos] at hu
  have hnorm := rootGroup_single_le_normalizer (steinbergExtras m F) s
  have hset := Subgroup.coe_mul_of_right_le_normalizer_left
    (posUnipotentExcept (rootDatum m F) s)
    ((rootDatum m F).rootGroup (Pi.single s 1)) hnorm
  have hmem : u ∈ (↑(posUnipotentExcept (rootDatum m F) s ⊔
      (rootDatum m F).rootGroup (Pi.single s 1)) :
      Set (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) := hu
  rw [hset] at hmem
  rw [Set.mem_mul] at hmem
  obtain ⟨v, hv, x, hx, huv⟩ := hmem
  refine ⟨x, hx, x⁻¹ * v * x, ?_, ?_⟩
  · simpa using ((Subgroup.mem_normalizer_iff.mp (inv_mem (hnorm hx))) v).mp hv
  · rw [← huv]; group

@[expose] noncomputable def curtisDatum :
    CurtisDatum (Matrix.SpecialLinearGroup (Fin (m + 1)) F) (curtisCoxeterSystem m) p where
  U := posUnipotent (rootDatum m F)
  L := negUnipotent (rootDatum m F)
  H := ⨆ k, torus m F k
  X k := rootGroup m F (Pi.single k 1)
  Y k := rootGroup m F (-Pi.single k 1)
  Us k := posUnipotentExcept (rootDatum m F) k
  Q k := negUnipotentExcept (rootDatum m F) k
  n k := weylRep m F k
  nW := fun w => nrep (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
    (isCTGroupDatum m F) w
  isPGroup_U := by
    exact isPGroup_iSup_pos (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (steinbergExtras m F) (fun γ hγ => isPGroup_rootGroup_charP m F p hγ)
  isPGroup_L := by
    have hset : posSet (rootDatum m F).roots (-htHom) =
        {γ | γ ∈ (rootDatum m F).roots ∧ ht γ < 0} := by
      ext γ
      simp [posSet, htHom_apply]
    have h := isPGroup_iSup_posSet (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (steinbergExtras m F) (fun γ hγ => isPGroup_rootGroup_charP m F p hγ) (-htHom)
    rw [hset] at h
    change IsPGroup p ↥(⨆ γ ∈ {γ | γ ∈ (rootDatum m F).roots ∧ ht γ < 0},
      (rootDatum m F).rootGroup γ)
    exact h
  U_inf_L := posUnipotent_inf_negUnipotent (steinbergExtras m F)
  H_comm := fun a ha b hb => iSup_torus_comm m F ha hb
  H_normU := fun h hh u hu =>
    (Subgroup.mem_normalizer_iff.mp (iSup_torus_le_normalizer_posUnipotent m F hh) u).mp hu
  H_normU' := fun h hh u hu => by
    have h := (Subgroup.mem_normalizer_iff.mp
      (iSup_torus_le_normalizer_posUnipotent m F (inv_mem hh)) u).mp hu
    simpa [inv_inv] using h
  H_normL := fun h hh l hl =>
    (Subgroup.mem_normalizer_iff.mp (iSup_torus_le_normalizer_negUnipotent m F hh) l).mp hl
  H_normX := fun s h hh x hx =>
    (Subgroup.mem_normalizer_iff.mp
      (iSup_torus_le_normalizer_rootGroup m F ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem s) hh) x).mp hx
  H_normQ := fun s h hh q hq =>
    (Subgroup.mem_normalizer_iff.mp (iSup_torus_le_normalizer_negUnipotentExcept m F s hh) q).mp hq
  X_le := fun s => by
    exact rootGroup_le_posUnipotent (D := rootDatum m F) ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem s) (ht_single_pos (D := rootDatum m F) s)
  X_ne_bot := fun s => rootGroup_single_ne_bot m F s
  U_eq := fun s u hu => U_eq_aux m F s u hu
  Us_le := fun s => by
    exact posUnipotentExcept_le_posUnipotent (D := rootDatum m F) s
  X_normUs := fun s x hx v hv => by
    change x * v * x⁻¹ ∈ posUnipotentExcept (rootDatum m F) s
    exact ((Subgroup.mem_normalizer_iff.mp
      (rootGroup_single_le_normalizer (steinbergExtras m F) s hx)) v).mp hv
  n_normUs := fun s v hv => by
    change weylRep m F s * v * (weylRep m F s)⁻¹ ∈ posUnipotentExcept (rootDatum m F) s
    exact conj_n_mem_posUnipotentExcept (D := rootDatum m F) (n := weylRep m F)
      (H := torus m F) (isCTGroupDatum m F) s hv
  n_normUs' := by
    intro s v hv
    have hsq : weylRep m F s * weylRep m F s ∈ (⨆ k, torus m F k) := by
      rw [← pow_two]
      exact Subgroup.mem_iSup_of_mem s ((isCTGroupDatum m F).sq_mem s)
    have hW : (weylRep m F s * weylRep m F s)⁻¹ ∈ (⨆ k, torus m F k) := inv_mem hsq
    have hUs : (⨆ k, torus m F k) ≤ Subgroup.normalizer
        (posUnipotentExcept (rootDatum m F) s : Set _) := by
      refine le_normalizer_iSup₂ fun h hh γ hγ y hy => ?_
      exact Subgroup.mem_iSup_of_mem γ (Subgroup.mem_iSup_of_mem hγ
        ((Subgroup.mem_normalizer_iff.mp
          (iSup_torus_le_normalizer_rootGroup m F hγ.1.1 hh) y).mp hy))
    have e : (weylRep m F s)⁻¹ * v * weylRep m F s =
        (weylRep m F s * weylRep m F s)⁻¹ *
          (weylRep m F s * v * (weylRep m F s)⁻¹) *
          ((weylRep m F s * weylRep m F s)⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hUs hW)
      (weylRep m F s * v * (weylRep m F s)⁻¹)).mp
      (conj_n_mem_posUnipotentExcept (D := rootDatum m F) (n := weylRep m F)
        (H := torus m F) (isCTGroupDatum m F) s hv)
  Y_le := fun s => by
    rw [negUnipotent_eq_sup (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (steinbergExtras m F) s]
    exact le_sup_right
  Q_le := fun s => by
    exact negUnipotentExcept_le_negUnipotent (D := rootDatum m F) s
  L_le := by
    intro s
    rw [negUnipotent_eq_sup (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
      (steinbergExtras m F) s, sup_comm]
    exact le_rfl
  X_normQ := fun s x hx q hq => by
    change x * q * x⁻¹ ∈ negUnipotentExcept (rootDatum m F) s
    exact ((Subgroup.mem_normalizer_iff.mp
      (rootGroup_single_le_normalizer_negExcept (steinbergExtras m F) s hx)) q).mp hq
  Y_normQ := fun s y hy q hq => by
    change y * q * y⁻¹ ∈ negUnipotentExcept (rootDatum m F) s
    exact ((Subgroup.mem_normalizer_iff.mp
      (rootGroup_neg_single_le_normalizer_negExcept (steinbergExtras m F) s hy)) q).mp hq
  n_normQ := fun s q hq => by
    change weylRep m F s * q * (weylRep m F s)⁻¹ ∈ negUnipotentExcept (rootDatum m F) s
    exact conj_n_mem_negUnipotentExcept (D := rootDatum m F) (n := weylRep m F)
      (H := torus m F) (isCTGroupDatum m F) s hq
  n_conjX := by
    intro s x hx
    have h := ActsAs.conj_mem (D := rootDatum m F)
      (actsAs_n (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
        (isCTGroupDatum m F) s)
      ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem s) hx
    have harg : (weylAction (isFiniteType_A m)
        ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple s))
        (Pi.single s 1) = -Pi.single s 1 :=
      weylAction_simple_single (isFiniteType_A m) s
    convert h
    exact congrArg (rootGroup m F) harg.symm
  n_conjY := by
    intro s y hy
    have h := ActsAs.conj_mem (D := rootDatum m F)
      (actsAs_n (D := rootDatum m F) (n := weylRep m F) (H := torus m F)
        (isCTGroupDatum m F) s)
      ((RootSystem.ofCartan (isFiniteType_A m) ∅).neg_mem _
        ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem s)) hy
    have harg : (weylAction (isFiniteType_A m)
        ((coxeterMatrix (isFiniteType_A m)).toCoxeterSystem.simple s))
        (-Pi.single s 1) = Pi.single s 1 := by
      rw [map_neg, weylAction_simple_single (isFiniteType_A m) s, neg_neg]
    convert h
    exact congrArg (rootGroup m F) harg.symm
  n_sq := fun s => by
    change weylRep m F s * weylRep m F s ∈ ⨆ k, torus m F k
    rw [← pow_two]
    exact Subgroup.mem_iSup_of_mem s ((isCTGroupDatum m F).sq_mem s)
  n_normH := by
    intro s h hh
    refine Subgroup.iSup_induction (C := fun x => weylRep m F s * x * (weylRep m F s)⁻¹ ∈
      (⨆ k, torus m F k)) (S := fun k => torus m F k) hh ?_ ?_ ?_
    · intro k x hx
      exact (show torus m F s ⊔ torus m F k ≤ ⨆ l, torus m F l from
        sup_le (le_iSup (fun l => torus m F l) s) (le_iSup (fun l => torus m F l) k))
        ((isCTGroupDatum m F).conj_H_mem s k x hx)
    · simp
    · intro x y hx hy
      have e : weylRep m F s * (x * y) * (weylRep m F s)⁻¹ =
          (weylRep m F s * x * (weylRep m F s)⁻¹) *
            (weylRep m F s * y * (weylRep m F s)⁻¹) := by group
      rw [e]
      exact mul_mem hx hy
  phi := fun s x => phiVal m F s x
  psi := fun s x => phiVal m F s x
  phi_mem := fun s x hx hx1 => phiVal_mem m F s hx hx1
  psi_mem := fun s x hx hx1 => phiVal_mem m F s hx hx1
  phi_spec := fun s x hx hx1 => phiVal_spec m F s hx hx1
  psi_spec := fun s x hx hx1 => psiVal_spec m F s hx hx1
  bruhatY := fun s y hy hy1 => bruhatY_spec m F s hy hy1
  nW_one := nW_one m F
  nW_simple_mul := fun w s h => nW_simple_mul m F w s h
  nW_conj := fun w s h x hx => nW_conj m F w s h hx
  heckeDeg_mul := fun w s h => heckeDeg_mul m F w s h
  cover := fun g => cover m F g


omit [Fact (Nat.Prime p)] in
theorem mem_curtisDatum_U_iff {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (curtisDatum m F p).U ↔
      (∀ i, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1) ∧
        ∀ i j, j < i → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  change g ∈ posUnipotent (rootDatum m F) ↔ _
  rw [mem_posUnipotent_iff (m := m) F]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

omit [Fact (Nat.Prime p)] in
theorem mem_curtisDatum_L_iff {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (curtisDatum m F p).L ↔
      (∀ i, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i = 1) ∧
        ∀ i j, i < j → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  change g ∈ negUnipotent (rootDatum m F) ↔ _
  rw [mem_negUnipotent_iff (m := m) F]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

omit [Fact (Nat.Prime p)] in
theorem mem_curtisDatum_H_iff {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (curtisDatum m F p).H ↔
      ∀ i j, i ≠ j → (g : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j = 0 := by
  change g ∈ (⨆ k, torus m F k) ↔ _
  rw [mem_iSup_torus_iff m F]
  exact Iff.rfl

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_X (k : Fin m) {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (curtisDatum m F p).X k ↔
      ∃ c : F, SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c = g := by
  change g ∈ rootGroup m F (Pi.single k 1) ↔ _
  rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne) (by rw [toStd_single])]
  exact mem_rootSubgroup _ _

omit [Fact (Nat.Prime p)] in
theorem curtisDatum_Y (k : Fin m) {g : Matrix.SpecialLinearGroup (Fin (m + 1)) F} :
    g ∈ (curtisDatum m F p).Y k ↔
      ∃ c : F, SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne).symm c = g := by
  change g ∈ rootGroup m F (-Pi.single k 1) ↔ _
  rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne).symm (by
    rw [toStd_neg, toStd_single, neg_sub])]
  exact mem_rootSubgroup _ _

@[expose] noncomputable def coverId :
    CentralCoverData (curtisDatum m F p)
      (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (m + 1)) F)) p where
  cover :=
    { surj := Function.surjective_id
      ker_le := by
        rw [MonoidHom.ker_id]
        exact bot_le
      coprime := by
        rw [MonoidHom.ker_id, Subgroup.card_bot]
        exact Nat.coprime_one_left p }
  nhatW := (curtisDatum m F p).nW
  map_nhatW := fun _ => rfl
  nhatW_one := (curtisDatum m F p).nW_one
  nhatW_simple_mul := by
    intro w s h
    show (curtisDatum m F p).nW ((curtisCoxeterSystem m).simple s * w) =
      (curtisDatum m F p).nW ((curtisCoxeterSystem m).simple s) *
        (curtisDatum m F p).nW w
    rw [(curtisDatum m F p).nW_simple_mul w s h]
    rw [CentralCoverData.nW_simple]
  hcomm := fun a ha b hb => (curtisDatum m F p).H_comm a ha b hb

theorem coverId_nhatW (k : Fin m) :
    (coverId m F p).nhatW ((curtisCoxeterSystem m).simple k) = weylRep m F k := by
  change (curtisDatum m F p).nW ((curtisCoxeterSystem m).simple k) = weylRep m F k
  exact CentralCoverData.nW_simple (curtisDatum m F p) k

@[expose] noncomputable def rankOne :
    CoverRankOne (coverId m F p) (fun _ => F) where
  x k c := SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c
  y k c := SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne).symm c
  hh k u := hdiag m F k u
  x_mem := by
    intro k c
    refine (CentralCoverData.mem_lX
      (C := coverId m F p)).mpr ⟨?_, ?_⟩
    · change SpecialLinearGroup.transvection ((Fin.castSucc_lt_succ (i := k)).ne) c ∈
        rootGroup m F (Pi.single k 1)
      rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne) (by rw [toStd_single])]
      exact transvection_mem_rootSubgroup _ c
    · exact isPElt_of_mem_rootGroup_charP m F p
        ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem k)
        (by
          rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne) (by rw [toStd_single])]
          exact transvection_mem_rootSubgroup _ c)
  x_surj := by
    intro k g hg
    have hg' := (CentralCoverData.mem_lX
      (C := coverId m F p)).mp hg
    have hX : g ∈ (curtisDatum m F p).X k := hg'.1
    exact (curtisDatum_X m F p k).mp hX
  x_zero := by
    intro k
    exact SpecialLinearGroup.transvection_coeff_zero _
  x_inj := by
    intro k
    exact SpecialLinearGroup.transvection_injective _
  y_mem := by
    intro k c
    refine (CentralCoverData.mem_lL
      (C := coverId m F p)).mpr ⟨?_, ?_⟩
    · have hy : SpecialLinearGroup.transvection
          ((Fin.castSucc_lt_succ (i := k)).ne).symm c ∈ (curtisDatum m F p).Y k :=
        (curtisDatum_Y m F p k).mpr ⟨c, rfl⟩
      exact (curtisDatum m F p).Y_le k hy
    · exact isPElt_of_mem_rootGroup_charP m F p
        ((RootSystem.ofCartan (isFiniteType_A m) ∅).neg_mem _ ((RootSystem.ofCartan (isFiniteType_A m) ∅).single_mem k))
        (by
          rw [rootGroup_eq m F ((Fin.castSucc_lt_succ (i := k)).ne).symm (by
            rw [toStd_neg, toStd_single, neg_sub])]
          exact transvection_mem_rootSubgroup _ c)
  hh_mem := by
    intro k u
    exact (Subgroup.mem_comap).mpr (hdiag_mem_H m F k u)
  hh_mul := by
    intro k u v
    exact hdiag_mul m F k u v
  hh_one := by
    intro k
    exact hdiag_one m F k
  phi_id := by
    intro k u
    have hn : (coverId m F p).nhat k = weylRep m F k := by
      rw [CentralCoverData.nhat]
      exact coverId_nhatW m F p k
    have h := rankOne_upper m F k (u : F) u.ne_zero
    have hneg : (-u : Fˣ) = Units.mk0 (-(u : F)) (neg_ne_zero.mpr u.ne_zero) := Units.ext rfl
    simpa [hn, hneg] using h
  psi_id := by
    intro k u
    have hn : (coverId m F p).nhat k = weylRep m F k := by
      rw [CentralCoverData.nhat]
      exact coverId_nhatW m F p k
    have h := rankOne_conj m F k (u : F) u.ne_zero
    have hneg : (-u : Fˣ) = Units.mk0 (-(u : F)) (neg_ne_zero.mpr u.ne_zero) := Units.ext rfl
    simpa [hn, hneg] using h

omit [Fact (Nat.Prime p)] in
theorem hodd :
    ∀ h ∈ (curtisDatum m F p).H.comap (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (m + 1)) F)),
      IsPElt p h → h = 1 := by
  intro h hh hp
  have hh' : h ∈ ⨆ k, torus m F k := hh
  have hpowH : h ^ (Nat.card F - 1) = 1 := iSup_torus_pow_card_sub_one m F hh'
  have hp' : ∃ k, h ^ (p ^ k) = 1 := hp
  obtain ⟨k, hk⟩ := hp'
  have hdvdP : orderOf h ∣ p ^ k := orderOf_dvd_iff_pow_eq_one.mpr hk
  have hdvdF : orderOf h ∣ Nat.card F - 1 := orderOf_dvd_iff_pow_eq_one.mpr hpowH
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨n, hp', hn⟩ := FiniteField.card F p
  have hn' : Nat.card F = p ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card]; exact hn
  have hcop : Nat.Coprime (p ^ k) (Nat.card F - 1) := by
    rw [hn']
    have hnot : ¬ p ∣ p ^ (n : ℕ) - 1 := by
      intro hd
      have hpn : p ∣ p ^ (n : ℕ) := dvd_pow_self p (by exact ne_of_gt n.pos)
      have h1 : p ∣ 1 := by
        have hle : 1 ≤ p ^ (n : ℕ) := Nat.one_le_pow (n : ℕ) p (Nat.Prime.pos hp')
        have hsub := Nat.dvd_sub hpn hd
        have heq : p ^ (n : ℕ) - (p ^ (n : ℕ) - 1) = 1 := by omega
        rwa [heq] at hsub
      exact (Nat.Prime.not_dvd_one hp') h1
    exact (Nat.Prime.coprime_pow_of_not_dvd hp' hnot).symm
  have hone : orderOf h = 1 := by
    have hd := Nat.dvd_gcd hdvdP hdvdF
    have hcop' : Nat.gcd (p ^ k) (Nat.card F - 1) = 1 :=
      Nat.coprime_iff_gcd_eq_one.mp hcop
    rw [hcop'] at hd
    exact Nat.dvd_one.mp hd
  exact orderOf_eq_one_iff.mp hone

omit [Fact (Nat.Prime p)] in
theorem splitOver (k : Type) [Field k] [Algebra F k] :
    SplitOver k
      ((curtisDatum m F p).H.comap (MonoidHom.id (Matrix.SpecialLinearGroup (Fin (m + 1)) F))) :=
  splitOver_of_pow_card_sub_one (K := F) k
    (fun h hh => by
      have hh' : h ∈ ⨆ j, torus m F j := hh
      exact iSup_torus_pow_card_sub_one m F hh')

end

end CFSG.LieType.SpecialLinear

namespace CFSG.LieType.SpecialLinear

open Matrix CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.LieType.Universal
  CFSG.LieType.Universal.SpecialLinear CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
open scoped MatrixGroups

noncomputable section

variable (m : ℕ) (F : Type) [Field F] [Finite F] (p : ℕ) [Fact p.Prime] [CharP F p]

theorem exists_isCoverType_sl {k V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k,
      ∃ J : Finset (Fin m), IsCoverType (rankOne m F p) ρ y χ J := by
  have : Finite ((coxeterMatrix (isFiniteType_A m)).Group) :=
    Finite.of_equiv (Equiv.Perm (Fin (m + 1))) (CFSG.StandardType.typeAWeylEquiv m).toEquiv
  exact exists_isCoverType (D := curtisDatum m F p) (π := MonoidHom.id _)
    (C := coverId m F p) (R := rankOne m F p) (p := p) hρ (splitOver m F p k)

theorem isCoverType_unique_sl {k V : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [CharP k p] {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    (hρ : IsSimpleRep ρ) {y y' : V}
    {χ χ' : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J J' : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J)
    (ht' : IsCoverType (rankOne m F p) ρ y' χ' J') :
    (∀ h ∈ (curtisDatum m F p).H.comap (MonoidHom.id _), χ h = χ' h) ∧ J = J' := by
  have : Finite ((coxeterMatrix (isFiniteType_A m)).Group) :=
    Finite.of_equiv (Equiv.Perm (Fin (m + 1))) (CFSG.StandardType.typeAWeylEquiv m).toEquiv
  exact IsCoverType.unique (D := curtisDatum m F p) (π := MonoidHom.id _)
    (C := coverId m F p) (R := rankOne m F p) (p := p) hρ (splitOver m F p k) ht ht'

theorem iso_of_isCoverType_sl {k V V' : Type} [Field k] [Algebra F k] [AddCommGroup V] [Module k V]
    [AddCommGroup V'] [Module k V'] [CharP k p]
    {ρ : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V}
    {ρ' : Representation k (Matrix.SpecialLinearGroup (Fin (m + 1)) F) V'}
    (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ') {y : V} {y' : V'}
    {χ : Matrix.SpecialLinearGroup (Fin (m + 1)) F → k} {J : Finset (Fin m)}
    (ht : IsCoverType (rankOne m F p) ρ y χ J)
    (ht' : IsCoverType (rankOne m F p) ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : Matrix.SpecialLinearGroup (Fin (m + 1)) F) (v : V),
      β (ρ g v) = ρ' g (β v) := by
  have : Finite ((coxeterMatrix (isFiniteType_A m)).Group) :=
    Finite.of_equiv (Equiv.Perm (Fin (m + 1))) (CFSG.StandardType.typeAWeylEquiv m).toEquiv
  exact iso_of_isCoverType (D := curtisDatum m F p) (π := MonoidHom.id _)
    (C := coverId m F p) (R := rankOne m F p) (p := p)
    (hodd := hodd m F p) (hsplit := splitOver m F p k) (hρ := hρ) (hρ' := hρ')
    (ht := ht) (ht' := ht')

end

end CFSG.LieType.SpecialLinear
