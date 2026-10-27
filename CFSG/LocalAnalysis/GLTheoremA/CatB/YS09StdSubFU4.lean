module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.YS09StdSubF
public import CFSG.LocalAnalysis.GLTheoremA.CatB.Bridges

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA CFSG.GH74.Exceptional
  CFSG.LocalAnalysis.GLTheoremB Matrix

namespace StdU4

@[expose] def qA : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![0, 1; 2, 0]

@[expose] def qB : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, 1; 1, 2]

@[expose] def uM (a : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![1, a; 0, 1]

@[expose] def phi : QuaternionGroup 2 →* Matrix (Fin 2) (Fin 2) (ZMod 3) where
  toFun x := match x with
    | .a i => qA ^ i.val
    | .xa i => qB * qA ^ i.val
  map_one' := by decide
  map_mul' := by decide

theorem phi_injective : Function.Injective phi := by decide

theorem uM_conj_ex : ∀ a : ZMod 3, ∀ p : QuaternionGroup 2,
    ∃ p' : QuaternionGroup 2, uM a * phi p * uM (-a) = phi p' := by decide

noncomputable def cc (a : ZMod 3) (p : QuaternionGroup 2) : QuaternionGroup 2 :=
  (uM_conj_ex a p).choose

theorem uM_conj (a : ZMod 3) (p : QuaternionGroup 2) : uM a * phi p * uM (-a) = phi (cc a p) :=
  (uM_conj_ex a p).choose_spec

theorem cc_zero (p : QuaternionGroup 2) : cc 0 p = p := by
  apply phi_injective
  have h := uM_conj 0 p
  have h0 : uM 0 = 1 := by decide
  rw [← h]
  simp [h0]

@[expose] def UmQ (S : Matrix (Fin 2) (Fin 2) (ZMod 3)) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  Matrix.fromBlocks 1 S 0 1

@[expose] def SmQ (a b c : ZMod 3) : Matrix (Fin 2) (Fin 2) (ZMod 3) := !![a, b; b, c]

theorem EQ_mul : ∀ a b c a' b' c' : ZMod 3,
    UmQ (SmQ a b c) * UmQ (SmQ a' b' c') = UmQ (SmQ (a + a') (b + b') (c + c')) := by decide

theorem EQ_one : UmQ (SmQ 0 0 0) = 1 := by decide

theorem EQ_symp : ∀ a b c : ZMod 3,
    (UmQ (SmQ a b c)).transpose * Matrix.fromBlocks 0 1 (-1) 0 * UmQ (SmQ a b c) =
      Matrix.fromBlocks 0 1 (-1) 0 := by decide

@[expose] def eSp (a b c : ZMod 3) : StatedSp 2 (ZMod 3) :=
  mkSpG (UmQ (SmQ a b c)) (UmQ (SmQ (-a) (-b) (-c)))
    (by rw [EQ_mul, add_neg_cancel, add_neg_cancel, add_neg_cancel, EQ_one])
    (by rw [EQ_mul, neg_add_cancel, neg_add_cancel, neg_add_cancel, EQ_one])
    (EQ_symp a b c)

theorem eSp_mul (a b c a' b' c' : ZMod 3) :
    eSp a b c * eSp a' b' c' = eSp (a + a') (b + b') (c + c') :=
  Subtype.ext (Units.ext (EQ_mul a b c a' b' c'))

@[expose] def TphiQ : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* PSp43 :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3)).subgroupOf
    (StatedSp 2 (ZMod 3)))).comp
    (MonoidHom.mk' (fun v => eSp v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2) fun x y =>
      (eSp_mul _ _ _ _ _ _).symm)

theorem TphiQ_key : ∀ a b c : ZMod 3,
    (∃ k : ZMod 3, k ≠ 0 ∧ UmQ (SmQ a b c) = k • 1) → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide

theorem TphiQ_injective : Function.Injective TphiQ := by
  rw [injective_iff_map_eq_one]
  intro v hv
  have hv' : TphiQ v = (QuotientGroup.mk (eSp v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2) : PSp43) := rfl
  rw [hv', QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at hv
  obtain ⟨k, hk⟩ := MonoidHom.mem_range.1 hv
  have h' := congrArg Units.val hk
  have hm : UmQ (SmQ v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2) = (k : ZMod 3) • 1 := by
    have h2 : ((eSp v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2 : StatedSp 2 (ZMod 3)) :
        GL (Fin 2 ⊕ Fin 2) (ZMod 3)).val = UmQ (SmQ v.toAdd.1 v.toAdd.2.1 v.toAdd.2.2) := rfl
    rw [← h2, ← h']
    ext i j
    by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply,
      Matrix.one_apply, hij]
  have hz := TphiQ_key _ _ _ ⟨k, k.ne_zero, hm⟩
  exact Multiplicative.toAdd.injective (Prod.ext hz.1 (Prod.ext hz.2.1 hz.2.2))

def psi0 (x : QuaternionGroup 2 × QuaternionGroup 2) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 3) :=
  pb ![phi x.1, phi x.2]

theorem psi0_mul (x y : QuaternionGroup 2 × QuaternionGroup 2) :
    psi0 (x * y) = psi0 x * psi0 y := by
  unfold psi0
  rw [pb_mul]
  congr 1
  funext i
  fin_cases i <;> simp [map_mul]

theorem psi0_one : psi0 1 = 1 := by
  unfold psi0
  have h : (![phi (1 : QuaternionGroup 2 × QuaternionGroup 2).1,
      phi (1 : QuaternionGroup 2 × QuaternionGroup 2).2] : Fin 2 → _) = fun _ => 1 := by
    funext i; fin_cases i <;> simp
  rw [h, pb_one]

theorem psi0_symp : ∀ x : QuaternionGroup 2 × QuaternionGroup 2,
    (psi0 x).transpose * Matrix.fromBlocks 0 1 (-1) 0 * psi0 x = Matrix.fromBlocks 0 1 (-1) 0 := by
  decide

def sp4 (x : QuaternionGroup 2 × QuaternionGroup 2) : StatedSp 2 (ZMod 3) :=
  mkSpG (psi0 x) (psi0 x⁻¹)
    (by rw [← psi0_mul, mul_inv_cancel, psi0_one])
    (by rw [← psi0_mul, inv_mul_cancel, psi0_one]) (psi0_symp x)

def psiHom : QuaternionGroup 2 × QuaternionGroup 2 →* StatedSp 2 (ZMod 3) :=
  MonoidHom.mk' sp4 fun x y => Subtype.ext (Units.ext (psi0_mul x y))

def Psi : QuaternionGroup 2 × QuaternionGroup 2 →* PSp43 :=
  (QuotientGroup.mk' ((StatedScalars (Fin 2 ⊕ Fin 2) (ZMod 3)).subgroupOf
    (StatedSp 2 (ZMod 3)))).comp psiHom

def zz : QuaternionGroup 2 × QuaternionGroup 2 := (QuaternionGroup.a 2, QuaternionGroup.a 2)

theorem kernel_dec : ∀ x : QuaternionGroup 2 × QuaternionGroup 2,
    (∃ c : ZMod 3, c ≠ 0 ∧ psi0 x = c • 1) → x = 1 ∨ x = zz := by
  decide

theorem Psi_eq_one {x : QuaternionGroup 2 × QuaternionGroup 2} (h : Psi x = 1) :
    x = 1 ∨ x = zz := by
  rw [Psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf] at h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.1 h
  apply kernel_dec x
  refine ⟨(c : ZMod 3), c.ne_zero, ?_⟩
  have h' := congrArg Units.val hc
  have h2 : ((psiHom x : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)).val = psi0 x := rfl
  rw [← h2, ← h']
  ext i j
  by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply,
    Matrix.one_apply, hij]

theorem Psi_zz : Psi zz = 1 := by
  rw [Psi, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
    Subgroup.mem_subgroupOf]
  refine MonoidHom.mem_range.2 ⟨-1, Units.ext ?_⟩
  have h : psi0 zz = (-1 : ZMod 3) • 1 := by decide
  have h2 : ((psiHom zz : StatedSp 2 (ZMod 3)) : GL (Fin 2 ⊕ Fin 2) (ZMod 3)).val = psi0 zz := rfl
  rw [h2, h]
  ext i j
  by_cases hij : i = j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply,
    Matrix.one_apply, hij]

theorem ker_eq : Psi.ker = Subgroup.zpowers zz := by
  apply le_antisymm
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rcases Psi_eq_one hx with rfl | rfl
    · exact one_mem _
    · exact Subgroup.mem_zpowers zz
  · rw [Subgroup.zpowers_le]
    exact MonoidHom.mem_ker.2 Psi_zz

theorem card_zpowers_zz : Nat.card (Subgroup.zpowers zz) = 2 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
  exact orderOf_eq_prime (by decide) (by decide)

theorem card_domain : Nat.card (QuaternionGroup 2 × QuaternionGroup 2) = 2 ^ 6 := by
  rw [Nat.card_prod, Nat.card_eq_fintype_card, QuaternionGroup.card]
  norm_num

theorem card_T4 : Nat.card Psi.range = 2 ^ 5 := by
  have h := Subgroup.card_ker_mul_card_range Psi
  rw [ker_eq, card_zpowers_zz, card_domain] at h
  omega

theorem isPGroup_T4 : IsPGroup 2 Psi.range :=
  IsPGroup.of_card card_T4

theorem US_pb : ∀ a c : ZMod 3, UmQ (SmQ a 0 c) = pb ![uM a, uM c] := by decide

theorem US_pb' : ∀ a c : ZMod 3, UmQ (SmQ (-a) (-0) (-c)) = pb ![uM (-a), uM (-c)] := by decide

theorem conj_sp4 (a c : ZMod 3) (y : QuaternionGroup 2 × QuaternionGroup 2) :
    eSp a 0 c * sp4 y * (eSp a 0 c)⁻¹ = sp4 (cc a y.1, cc c y.2) := by
  apply Subtype.ext
  apply Units.ext
  change UmQ (SmQ a 0 c) * psi0 y * UmQ (SmQ (-a) (-0) (-c)) = psi0 (cc a y.1, cc c y.2)
  rw [US_pb, US_pb']
  unfold psi0
  rw [pb_mul, pb_mul]
  congr 1
  funext i
  fin_cases i <;> simp [uM_conj]

theorem TphiQ_emb13 (x : Multiplicative (ZMod 3 × ZMod 3)) :
    TphiQ (emb13 x) = QuotientGroup.mk (eSp x.toAdd.1 0 x.toAdd.2) := rfl

theorem conj_Psi (x : Multiplicative (ZMod 3 × ZMod 3)) (y : QuaternionGroup 2 × QuaternionGroup 2) :
    TphiQ (emb13 x) * Psi y * (TphiQ (emb13 x))⁻¹ = Psi (cc x.toAdd.1 y.1, cc x.toAdd.2 y.2) := by
  have key := conj_sp4 x.toAdd.1 x.toAdd.2 y
  rw [TphiQ_emb13]
  have hP : Psi y = QuotientGroup.mk (sp4 y) := rfl
  have hQ : Psi (cc x.toAdd.1 y.1, cc x.toAdd.2 y.2) =
      QuotientGroup.mk (sp4 (cc x.toAdd.1 y.1, cc x.toAdd.2 y.2)) := rfl
  rw [hP, hQ, ← key]
  rfl

theorem hFN_T4 (x : Multiplicative (ZMod 3 × ZMod 3)) (t : PSp43) (ht : t ∈ Psi.range) :
    TphiQ (emb13 x) * t * (TphiQ (emb13 x))⁻¹ ∈ Psi.range := by
  obtain ⟨y, rfl⟩ := MonoidHom.mem_range.1 ht
  rw [conj_Psi]
  exact MonoidHom.mem_range.2 ⟨_, rfl⟩

theorem hTc_T4 : ∃ t ∈ Psi.range, ∃ x : Multiplicative (ZMod 3 × ZMod 3),
    t * TphiQ (emb13 x) ≠ TphiQ (emb13 x) * t := by
  refine ⟨Psi (QuaternionGroup.a 1, 1), MonoidHom.mem_range.2 ⟨_, rfl⟩,
    Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)), ?_⟩
  intro h
  have hc : TphiQ (emb13 (Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)))) *
      Psi (QuaternionGroup.a 1, 1) *
      (TphiQ (emb13 (Multiplicative.ofAdd ((1 : ZMod 3), (0 : ZMod 3)))))⁻¹ =
      Psi (QuaternionGroup.a 1, 1) := by
    rw [← h, mul_inv_cancel_right]
  rw [conj_Psi] at hc
  have hc' : Psi (cc 1 (QuaternionGroup.a 1), cc 0 1) = Psi (QuaternionGroup.a 1, 1) := hc
  have hu : Psi ((cc 1 (QuaternionGroup.a 1), cc 0 1)⁻¹ *
      (QuaternionGroup.a 1, (1 : QuaternionGroup 2))) = 1 := by
    rw [map_mul, map_inv, hc', inv_mul_cancel]
  have hne : uM 1 * phi (QuaternionGroup.a 1) * uM (-1) ≠ phi (QuaternionGroup.a 1) := by decide
  rcases Psi_eq_one hu with h1 | h1
  · have e1 : (cc 1 (QuaternionGroup.a 1))⁻¹ * QuaternionGroup.a 1 = 1 := congrArg Prod.fst h1
    have hc1 : cc 1 (QuaternionGroup.a 1) = QuaternionGroup.a 1 := inv_mul_eq_one.1 e1
    apply hne
    rw [uM_conj, hc1]
  · have e2 : (cc 0 1)⁻¹ * 1 = QuaternionGroup.a 2 := congrArg Prod.snd h1
    rw [cc_zero, inv_one, mul_one] at e2
    revert e2
    decide

theorem card_center_dvd_two_u4two (hGA : CFSG.Open.GriessAllModelsStatement) {G : Type} [Group G]
    [Finite G] {K : Subgroup G} (hK : CFSG.Open.IsQuasisimple ↥K)
    (h : catalogIs (↥K ⧸ Subgroup.center ↥K) S9.isU4two) :
    Nat.card (Subgroup.center ↥K) ∣ 2 := by
  obtain ⟨q, hv, hq2, ⟨e⟩⟩ := lieIndex_isU4two h
  obtain ⟨h1, h2⟩ := primePower_eq_of_card_eq Nat.prime_two (s := 1) (by norm_num)
    (hq2.trans (by norm_num))
  have hm := lieModel_twistedA' 3 q hv e
  rw [h1, h2] at hm
  have hdvd := card_center_dvd_of_table hGA hK hm (a := 1) (b := 1) (c := 2) (d := 1)
    (by decide) (by decide) (by norm_num)
  exact hdvd.trans (by norm_num)

end StdU4

end CFSG.LocalAnalysis.GLTheoremA.CatB
