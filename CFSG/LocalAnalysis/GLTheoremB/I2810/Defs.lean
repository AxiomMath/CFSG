module

public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLBasic
public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalMcLHeart
public import CFSG.LocalAnalysis.ComponentInitial.LinearIsometry
public import CFSG.LocalAnalysis.GLTheoremB.Prop95IvDefs
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.RankThree.PartTwo.NotationBlocks

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
open scoped commutatorElement

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810

section Defs
variable {X : Type} [Group X]

structure Setup28 (W K S : Subgroup X) [W.Normal] : Prop where
  hW : IsPGroup 2 W
  hC : Subgroup.centralizer (W : Set X) ≤ W
  hK : IsTwoPrimeCompOf K
  hO : CFSG.pCore 2 ↥(bar W K) = ⊥
  hS : IsPGroup 2 S
  hN : S ≤ Subgroup.normalizer (K : Set X)
  hWS : W ≤ S

@[expose] def kerAct (W K S : Subgroup X) [W.Normal] : Subgroup X where
  carrier := {s | s ∈ S ∧ ∀ k ∈ K, ⁅s, k⁆ ∈ W}
  one_mem' := ⟨S.one_mem, fun k _ => by simpa using W.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haS, ha⟩ ⟨hbS, hb⟩
    refine ⟨S.mul_mem haS hbS, fun k hk => ?_⟩
    have h1 : ⁅a * b, k⁆ = (a * ⁅b, k⁆ * a⁻¹) * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb k hk) a) (ha k hk)
  inv_mem' := by
    rintro a ⟨haS, ha⟩
    refine ⟨S.inv_mem haS, fun k hk => ?_⟩
    have h1 : ⁅a⁻¹, k⁆ = a⁻¹ * (⁅a, k⁆⁻¹) * a := by
      simp only [commutatorElement_def]; group
    rw [h1]
    simpa using Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem (ha k hk)) a⁻¹

@[expose] def omegaZ (T : Subgroup X) : Subgroup X where
  carrier := {v | v ∈ T ∧ (∀ w ∈ T, v * w = w * v) ∧ v ^ 2 = 1}
  one_mem' := ⟨T.one_mem, fun w _ => by simp, by simp⟩
  mul_mem' := by
    rintro a b ⟨haT, hac, ha2⟩ ⟨hbT, hbc, hb2⟩
    refine ⟨T.mul_mem haT hbT, fun w hw => ?_, ?_⟩
    · rw [mul_assoc, hbc w hw, ← mul_assoc, hac w hw, mul_assoc]
    · have hab : a * b = b * a := hac b hbT
      calc (a * b) ^ 2 = a * b * (a * b) := by rw [pow_two]
        _ = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [← hab]
        _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
        _ = 1 := by rw [ha2, hb2, one_mul]
  inv_mem' := by
    rintro a ⟨haT, hac, ha2⟩
    refine ⟨T.inv_mem haT, fun w hw => ?_, ?_⟩
    · have := hac w hw
      calc a⁻¹ * w = a⁻¹ * (w * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * w) * a⁻¹ := by rw [← this]
        _ = w * a⁻¹ := by group
    · rw [inv_pow, ha2, inv_one]

@[expose] def vOf (W K S : Subgroup X) [W.Normal] : Subgroup X := omegaZ (kerAct W K S)

@[expose] def zPre (W K : Subgroup X) [W.Normal] : Subgroup X where
  carrier := {k | k ∈ K ∧ ∀ k' ∈ K, ⁅k, k'⁆ ∈ W}
  one_mem' := ⟨K.one_mem, fun k _ => by simpa using W.one_mem⟩
  mul_mem' := by
    rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
    refine ⟨K.mul_mem haK hbK, fun k hk => ?_⟩
    have h1 : ⁅a * b, k⁆ = (a * ⁅b, k⁆ * a⁻¹) * ⁅a, k⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    exact W.mul_mem (Subgroup.Normal.conj_mem inferInstance _ (hb k hk) a) (ha k hk)
  inv_mem' := by
    rintro a ⟨haK, ha⟩
    refine ⟨K.inv_mem haK, fun k hk => ?_⟩
    have h1 : ⁅a⁻¹, k⁆ = a⁻¹ * (⁅a, k⁆⁻¹) * a := by
      simp only [commutatorElement_def]; group
    rw [h1]
    simpa using Subgroup.Normal.conj_mem inferInstance _ (W.inv_mem (ha k hk)) a⁻¹

abbrev indAut (W K B : Subgroup X) [W.Normal] : Subgroup (MulAut ↥(bar W K)) :=
  inducedAutGroup (bar W B) (bar W K)

@[expose] def IndInner (W K : Subgroup X) [W.Normal] (a : X) : Prop :=
  ∃ k ∈ K, ∀ x ∈ K, a * x * a⁻¹ * (k * x * k⁻¹)⁻¹ ∈ W

@[expose] def TransvOn (V : Subgroup X) (a : X) : Prop :=
  ∃ u ∈ V, u ≠ 1 ∧ ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = v * u

@[expose] noncomputable def modC (W K : Subgroup X) [W.Normal] :
    ↥K →* ↥(bar W K) ⧸ Subgroup.center ↥(bar W K) :=
  (QuotientGroup.mk' (Subgroup.center ↥(bar W K))).comp (toBar W K)

@[expose] def Inverts (W K : Subgroup X) [W.Normal] (a : X) (P : ℕ → Prop) : Prop :=
  ∃ x : ↥K, Odd (orderOf (modC W K x)) ∧ P (orderOf (modC W K x)) ∧
    a * (x : X) * a⁻¹ * (x : X) ∈ zPre W K

structure SFBase (K V U₁ U₂ : Subgroup X) : Prop where
  le : U₂ ≤ U₁ ∧ U₁ ≤ V
  inv₁ : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁
  inv₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ ∈ U₂
  triv₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ = x
  comm_le : ∀ k ∈ K, ∀ v ∈ V, ⁅v, k⁆ ∈ U₁
  nontriv : ∃ k ∈ K, ∃ x ∈ U₁, ⁅x, k⁆ ∉ U₂

structure SingleFactor (K V U₁ U₂ : Subgroup X) : Prop extends SFBase K V U₁ U₂ where
  irred : ∀ Y : Subgroup X, U₂ ≤ Y → Y ≤ U₁ → (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) →
    Y = U₂ ∨ Y = U₁

structure ASection (a : X) (U₁ U₂ : Subgroup X) : Prop where
  inv₁ : ∀ x ∈ U₁, a * x * a⁻¹ ∈ U₁
  inv₂ : ∀ x ∈ U₂, a * x * a⁻¹ ∈ U₂
  tr : ∃ u ∈ U₁, u ∉ U₂ ∧ ∀ x ∈ U₁, a * x * a⁻¹ * x⁻¹ ∈ U₂ ∨ a * x * a⁻¹ * x⁻¹ * u⁻¹ ∈ U₂
  nt : ∃ x ∈ U₁, a * x * a⁻¹ * x⁻¹ ∉ U₂

structure TransSectionM (K V U₁ U₂ : Subgroup X) (a : X) : Prop extends SFBase K V U₁ U₂ where
  asec : ASection a U₁ U₂
  irredM : ∀ Y : Subgroup X, U₂ ≤ Y → Y ≤ U₁ → (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) →
    (∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = U₂ ∨ Y = U₁

structure TransSection (K V U₁ U₂ : Subgroup X) (a : X) : Prop extends SingleFactor K V U₁ U₂ where
  asec : ASection a U₁ U₂

@[expose] def fixV' {V : Type} [Group V] (X : Subgroup (MulAut V)) : Subgroup V where
  carrier := {v | ∀ x ∈ X, x v = v}
  one_mem' := fun x _ => map_one x
  mul_mem' := fun {a b} ha hb x hx => by rw [map_mul, ha x hx, hb x hx]
  inv_mem' := fun {a} ha x hx => by rw [map_inv, ha x hx]

@[expose] def commV' {V : Type} [Group V] (X : Subgroup (MulAut V)) : Subgroup V :=
  Subgroup.closure {c | ∃ x ∈ X, ∃ v : V, c = x v * v⁻¹}

end Defs

section Step0
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

structure Red28 (W K S : Subgroup X) [W.Normal] : Prop where
  quasi : IsQuasisimple ↥(bar W K)
  o2K : pCoreOf 2 K = K ⊓ W
  w1_le : W ≤ kerAct W K S
  w1_S : kerAct W K S ≤ S
  w1_nrm : ∀ n ∈ K ⊔ S, ∀ w ∈ kerAct W K S, n * w * n⁻¹ ∈ kerAct W K S
  w1_cent : Subgroup.centralizer (kerAct W K S : Set X) ≤ kerAct W K S
  k_w1 : K ⊓ kerAct W K S = K ⊓ W
  v_elem : IsElemAbelian 2 (vOf W K S)
  v_le : vOf W K S ≤ kerAct W K S
  v_nrm : ∀ n ∈ K ⊔ S, ∀ v ∈ vOf W K S, n * v * n⁻¹ ∈ vOf W K S
  v_nt : ¬ K ≤ Subgroup.centralizer (vOf W K S : Set X)
  cent_comm : ∀ c ∈ K ⊔ S, (∀ v ∈ vOf W K S, c * v = v * c) → ∀ k ∈ K, ⁅c, k⁆ ∈ W

structure Off28 (W K S A : Subgroup X) [W.Normal] : Prop where
  isMax : Quasithin.IsMaxElemAbelian S A
  not_le : ¬ A ≤ kerAct W K S
  off : (Subgroup.centralizer (A : Set X)).relIndex (vOf W K S) ≤ (kerAct W K S).relIndex A

end Step0

section Induced
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem indAut_mono {B B' : Subgroup X} (h : B ≤ B') : indAut W K B ≤ indAut W K B' :=
  Subgroup.map_mono (Subgroup.subgroupOf_mono _ (Subgroup.map_mono h))

end Induced

section ActionOnV
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

theorem N_le_normalizer_V (hR : Red28 W K S) :
    K ⊔ S ≤ Subgroup.normalizer (vOf W K S : Set X) := by
  intro n hn
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨fun hv => hR.v_nrm n hn v hv, fun hv => ?_⟩
  have h1 := hR.v_nrm n⁻¹ ((K ⊔ S).inv_mem hn) _ hv
  have h2 : n⁻¹ * (n * v * n⁻¹) * n⁻¹⁻¹ = v := by group
  rwa [h2] at h1

@[expose] noncomputable def vAct (hR : Red28 W K S) : ↥(K ⊔ S) →* MulAut ↥(vOf W K S) :=
  (vOf W K S).normalizerMonoidHom.comp (Subgroup.inclusion (N_le_normalizer_V hR))

@[expose] noncomputable def khOf (hR : Red28 W K S) : Subgroup (MulAut ↥(vOf W K S)) :=
  (K.subgroupOf (K ⊔ S)).map (vAct hR)

@[expose] noncomputable def ehOf (hR : Red28 W K S) (A : Subgroup X) : Subgroup (MulAut ↥(vOf W K S)) :=
  (A.subgroupOf (K ⊔ S)).map (vAct hR)

@[expose] noncomputable def kToKh (hR : Red28 W K S) : ↥K →* ↥(khOf hR) :=
  ((vAct hR).comp (Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S))).codRestrict (khOf hR)
    fun k => ⟨Subgroup.inclusion (le_sup_left : K ≤ K ⊔ S) k, k.2, rfl⟩

theorem vAct_sq (hR : Red28 W K S) {a : X} (haN : a ∈ K ⊔ S) (ha2 : a ^ 2 = 1) :
    vAct hR ⟨a, haN⟩ * vAct hR ⟨a, haN⟩ = 1 := by
  rw [← map_mul]
  have : (⟨a, haN⟩ : ↥(K ⊔ S)) * ⟨a, haN⟩ = 1 := Subtype.ext (by simpa [pow_two] using ha2)
  rw [this, map_one]

end ActionOnV

section LayerM
variable {V : Type} [Group V] [Finite V]

structure ASData (Kh Eh : Subgroup (MulAut V)) (n : ℕ) (π : ↥Kh →* ↥(alternatingGroup (Fin n)))
    (Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))) : Prop where
  hn : 5 ≤ n
  perf : ⁅Kh, Kh⁆ = Kh
  nt : Kh ≠ ⊥
  o2 : CFSG.pCore 2 ↥Kh = ⊥
  surj : Function.Surjective π
  ker : π.ker = Subgroup.center ↥Kh
  root : IsRootFour V₄ ∧ Vv ≤ V₄
  eab : IsElemAbelian 2 Eh
  norm : Eh ≤ Subgroup.normalizer (Kh : Set (MulAut V))
  faith : ∀ ε ∈ Eh, (∀ k ∈ Kh, ε * k = k * ε) → ε = 1
  act₁ : ∀ ε ∈ Eh, ∃ v ∈ Vv, ∀ k k' : ↥Kh, (k' : MulAut V) = ε * k * ε⁻¹ → π k' = v * π k * v⁻¹
  act₂ : ∀ v ∈ Vv, ∃ ε ∈ Eh, ∀ k k' : ↥Kh, (k' : MulAut V) = ε * k * ε⁻¹ → π k' = v * π k * v⁻¹
  off : (fixV' Eh).index ≤ Nat.card ↥Eh

structure A7Struct (Kh : Subgroup (MulAut V)) : Prop where
  center : Subgroup.center ↥Kh = ⊥
  comm16 : Nat.card ↥(commV' Kh) = 16
  irred : ∀ Y : Subgroup V, Y ≤ commV' Kh → (∀ g ∈ Kh, ∀ y ∈ Y, g y ∈ Y) →
    Y = ⊥ ∨ Y = commV' Kh

variable {Kh Eh : Subgroup (MulAut V)} {n : ℕ} {π : ↥Kh →* ↥(alternatingGroup (Fin n))}
  {Vv V₄ : Subgroup ↥(alternatingGroup (Fin n))}

theorem fixV'_le_of_le {X Y : Subgroup (MulAut V)} (h : X ≤ Y) : fixV' Y ≤ fixV' X :=
  fun _ hv x hx => hv x (h hx)

end LayerM

section Shared
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

@[expose] noncomputable def isoOfCenterBot {G H : Type*} [Group G] [Group H] (hZ : Subgroup.center G = ⊥)
    (e : (G ⧸ Subgroup.center G) ≃* H) : G ≃* H :=
  (QuotientGroup.quotientBot (G := G)).symm.trans ((QuotientGroup.quotientMulEquivOfEq hZ.symm).trans e)

end Shared

section CaseThree
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

structure A7X (W K S : Subgroup X) [W.Normal] : Prop where
  sf : SingleFactor K (vOf W K S) ⁅vOf W K S, K⁆ ⊥
  card16 : Nat.card ↥⁅vOf W K S, K⁆ = 16
  ztriv : ∀ z ∈ zPre W K, ∀ v ∈ vOf W K S, z * v * z⁻¹ = v

@[expose] noncomputable def piOf {n : ℕ}
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin n))) :
    ↥K →* ↥(alternatingGroup (Fin n)) :=
  (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥(bar W K)))).comp (toBar W K)

structure SOverV4 (W K S : Subgroup X) [W.Normal] (π : ↥K →* ↥(alternatingGroup (Fin 7)))
    (V₄ : Subgroup ↥(alternatingGroup (Fin 7))) : Prop where
  idx : (kerAct W K S).relIndex S = 4
  dec : ∀ s ∈ S, ∃ k : ↥K, (k : X) ∈ S ∧ s * (k : X)⁻¹ ∈ kerAct W K S ∧ π k ∈ V₄
  cov : ∀ v ∈ V₄, ∃ k : ↥K, (k : X) ∈ S ∧ π k = v

structure A5Data (W K S : Subgroup X) [W.Normal]
    (e : (↥(bar W K) ⧸ Subgroup.center ↥(bar W K)) ≃* ↥(alternatingGroup (Fin 7)))
    (V₄ B : Subgroup ↥(alternatingGroup (Fin 7))) (Ik : Subgroup X) : Prop where
  root : IsRootFour V₄
  sv : SOverV4 W K S (piOf e) V₄
  NK : ∀ g ∈ Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))),
    ∃ k : ↥K, (k : X) ∈ Subgroup.normalizer (S : Set X) ∧ piOf e k = g
  VB : V₄ ≤ B
  Bquot : Nonempty (↥B ≃* ↥(alternatingGroup (Fin 5)))
  Bgen : ∀ H : Subgroup ↥(alternatingGroup (Fin 7)), B ≤ H →
    Subgroup.normalizer (V₄ : Set ↥(alternatingGroup (Fin 7))) ≤ H → H = ⊤
  Ik_le : Ik ≤ K
  Ik_into : ∀ k : ↥K, (k : X) ∈ Ik → piOf e k ∈ B
  Ik_onto : ∀ b ∈ B, ∃ k : ↥K, (k : X) ∈ Ik ∧ piOf e k = b
  Ik_ker : ∀ k : ↥K, (k : X) ∈ Ik → piOf e k = 1 → (k : X) ∈ W

structure A5Frame (W K S : Subgroup X) [W.Normal] (I : Subgroup X) : Prop where
  w1_le : kerAct W K S ≤ I
  I_le : I ≤ K ⊔ S
  S_le : S ≤ I
  sylow : CFSG.QuasithinUnique.IsSylowTwoOf S I
  quot : Nonempty (↥I ⧸ CFSG.pCore 2 ↥I ≃* ↥(alternatingGroup (Fin 5)))
  o2 : pCoreOf 2 I = kerAct W K S
  dec : ∀ i ∈ I, ∃ k ∈ K, k ∈ I ∧ i * k⁻¹ ∈ kerAct W K S
  zker : I ⊓ zPre W K ≤ kerAct W K S
  gen : ∀ H : Subgroup X, H ≤ K → I ⊓ K ≤ H → (∀ k ∈ K, k ∈ Subgroup.normalizer (S : Set X) → k ∈ H) →
    K ≤ H ⊔ (K ⊓ kerAct W K S)

end CaseThree

section Core
open CFSG.ComponentClassification.OutcomeLocal CFSG.LocalAnalysis.ComponentInitial
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

@[expose] def OmegaModelWith {ι : Type} [Fintype ι] [DecidableEq ι] (Q : (ι → ZMod 2) → ZMod 2)
    (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) : Prop :=
  ∃ (θ : ↥K →* ↥(StatedOmega Q)) (t : GL ι (ZMod 2)),
    Function.Surjective θ ∧ (∀ k : ↥K, (k : X) ∈ W → θ k = 1) ∧ IsTransvection t ∧
    (∀ x, Q (Matrix.mulVec (t : Matrix ι ι (ZMod 2)) x) = Q x) ∧
    t ∈ Subgroup.normalizer (StatedOmega Q : Set (GL ι (ZMod 2))) ∧
    (∀ k k' : ↥K, (k' : X) = a * (k : X) * a⁻¹ →
      ((θ k' : ↥(StatedOmega Q)) : GL ι (ZMod 2)) =
        t * ((θ k : ↥(StatedOmega Q)) : GL ι (ZMod 2)) * t⁻¹) ∧
    ChiefFactorIso K U₁ U₂ θ
      (fun g v => Matrix.mulVec ((g : GL ι (ZMod 2)) : Matrix ι ι (ZMod 2)) v)

abbrev OmegaPlus (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) (n : ℕ) : Prop :=
  OmegaModelWith (StatedQuadPlus (n + 1) (ZMod 2)) W K a U₁ U₂

abbrev OmegaMinus (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) (n : ℕ) : Prop :=
  OmegaModelWith (StatedQuadMinus (n + 1) (ZMod 2) 1 1) W K a U₁ U₂

@[expose] def OmegaAny (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) (n : ℕ) : Prop :=
  OmegaPlus W K a U₁ U₂ n ∨ OmegaMinus W K a U₁ U₂ n

@[expose] def OmegaModel (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) : Prop :=
  ∃ n : ℕ, 1 ≤ n ∧ OmegaAny W K a U₁ U₂ n

@[expose] def AltModel (W K : Subgroup X) (a : X) (U₁ U₂ : Subgroup X) : Prop :=
  ∃ (m : ℕ) (θ : ↥K →* ↥(alternatingGroup (Fin m))) (σ : Equiv.Perm (Fin m)),
    5 ≤ m ∧ Function.Surjective θ ∧ (∀ k : ↥K, (k : X) ∈ W → θ k = 1) ∧ σ.IsSwap ∧
    (∀ k k' : ↥K, (k' : X) = a * (k : X) * a⁻¹ →
      ((θ k' : ↥(alternatingGroup (Fin m))) : Equiv.Perm (Fin m)) =
        σ * ((θ k : ↥(alternatingGroup (Fin m))) : Equiv.Perm (Fin m)) * σ⁻¹) ∧
    ChiefFactorIso K U₁ U₂ θ (fun g x => altHeartAct m (g : Equiv.Perm (Fin m)) x)

structure TLattice (K V : Subgroup X) (a u : X) (U₁ U₂ : Subgroup X) : Prop where
  u_mem : u ∈ U₁
  u_nmem : u ∉ U₂
  le : U₂ ≤ U₁ ∧ U₁ ≤ V
  tr : ∀ v ∈ V, a * v * a⁻¹ = v ∨ a * v * a⁻¹ = v * u
  inv₁ : ∀ k ∈ K, ∀ x ∈ U₁, k * x * k⁻¹ ∈ U₁
  inv₂ : ∀ k ∈ K, ∀ x ∈ U₂, k * x * k⁻¹ ∈ U₂
  ainv₁ : ∀ x ∈ U₁, a * x * a⁻¹ ∈ U₁
  ainv₂ : ∀ x ∈ U₂, a * x * a⁻¹ ∈ U₂
  genU₁ : ∀ Y : Subgroup X, u ∈ Y → (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) → U₁ ≤ Y
  a_fix₂ : ∀ x ∈ U₂, a * x * a⁻¹ = x
  irredM : ∀ Y : Subgroup X, U₂ ≤ Y → Y ≤ U₁ → (∀ k ∈ K, ∀ y ∈ Y, k * y * k⁻¹ ∈ Y) →
    (∀ y ∈ Y, a * y * a⁻¹ ∈ Y) → Y = U₂ ∨ Y = U₁

structure SecRepData {P : Type} [AddCommGroup P] [Module (ZMod 2) P] (M U₁ U₂ : Subgroup X)
    (ρ : ↥M →* LinearMap.GeneralLinearGroup (ZMod 2) P) (φ : ↥U₁ →* Multiplicative P) : Prop where
  surj : Function.Surjective φ
  ker : ∀ u : ↥U₁, φ u = 1 ↔ (u : X) ∈ U₂
  equiv : ∀ (g : ↥M) (u u' : ↥U₁), (u' : X) = (g : X) * (u : X) * (g : X)⁻¹ →
    φ u' = Multiplicative.ofAdd ((ρ g : P →ₗ[ZMod 2] P) (Multiplicative.toAdd (φ u)))

@[expose] def ShapeHyp {P : Type} [AddCommGroup P] [Module (ZMod 2) P]
    (H L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) : Prop :=
  1 ≤ Module.finrank (ZMod 2) P ∧
    (∃ T : Set (LinearMap.GeneralLinearGroup (ZMod 2) P),
      (∀ t ∈ T, IsF2Transvection t) ∧ H = Subgroup.closure T) ∧
    (∀ U : Submodule (ZMod 2) P,
      (∀ g ∈ H, ∀ u ∈ U, (g : P →ₗ[ZMod 2] P) u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
    L ≤ H ∧ L.relIndex H = 2 ∧ ⁅L, L⁆ = L ∧ L ≠ ⊥

abbrev Mof (K : Subgroup X) (a : X) : Subgroup X := K ⊔ Subgroup.zpowers a

@[expose] def aM (K : Subgroup X) (a : X) : ↥(Mof K a) := ⟨a, Subgroup.mem_sup_right (Subgroup.mem_zpowers a)⟩

@[expose] def rhoK {P : Type} [AddCommGroup P] [Module (ZMod 2) P] (K : Subgroup X) (a : X)
    (ρ : ↥(Mof K a) →* LinearMap.GeneralLinearGroup (ZMod 2) P) :
    ↥K →* ↥((K.subgroupOf (Mof K a)).map ρ) :=
  (ρ.comp (Subgroup.inclusion (le_sup_left : K ≤ Mof K a))).codRestrict _ fun k =>
    ⟨Subgroup.inclusion (le_sup_left : K ≤ Mof K a) k, k.2, rfl⟩

@[expose] def SymSpShape {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [FiniteDimensional (ZMod 2) P]
    (H : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) : Prop :=
  (Module.finrank (ZMod 2) P = 4 ∧ ∃ f : LinearMap.BilinForm (ZMod 2) P,
      f.Nondegenerate ∧ f.IsAlt ∧ H = bilinIsometryGroup f) ∨
    (Even (Module.finrank (ZMod 2) P) ∧
      ((∃ β : P ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) P + 1),
          H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
            (sumZeroRep (Module.finrank (ZMod 2) P + 1)).range) ∨
        ∃ β : P ≃ₗ[ZMod 2] sumZero (Module.finrank (ZMod 2) P + 2) ⧸
            onesLine (Module.finrank (ZMod 2) P + 2),
          H.map (LinearMap.GeneralLinearGroup.congrLinearEquiv β).toMonoidHom =
            (heartRep (Module.finrank (ZMod 2) P + 2)).range))

@[expose] def AltSwapConcl {P : Type} [AddCommGroup P] [Module (ZMod 2) P] [Finite P]
    (L : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) P)) (m : ℕ)
    (τ : LinearMap.GeneralLinearGroup (ZMod 2) P) : Prop :=
  ∃ (σ : Equiv.Perm (Fin m)) (φ : P ≃+ CFSG.RankThree.PartTwo.altHeart m)
      (θ : ↥L ≃* ↥(alternatingGroup (Fin m))), σ.IsSwap ∧
      (∀ (g : ↥L) (w : P) (x : CFSG.QuasithinUnique.evenWeight m),
        φ w = (x : CFSG.RankThree.PartTwo.altHeart m) →
          φ (((g : LinearMap.GeneralLinearGroup (ZMod 2) P) : P →ₗ[ZMod 2] P) w) =
            (CFSG.RankThree.PartTwo.evenWeightPerm (θ g : Equiv.Perm (Fin m)) x :
              CFSG.RankThree.PartTwo.altHeart m)) ∧
      (∀ g g' : ↥L, (g' : LinearMap.GeneralLinearGroup (ZMod 2) P) = τ * g * τ⁻¹ →
        (θ g' : Equiv.Perm (Fin m)) = σ * (θ g : Equiv.Perm (Fin m)) * σ⁻¹)

end Core

section CaseOneTwo
open CFSG.LocalAnalysis.GLTheoremB.Prop95Iv
variable {X : Type} [Group X] [Finite X] {W K S : Subgroup X} [W.Normal]

@[expose] def CentMax (W K S : Subgroup X) [W.Normal] (a : X) : Prop :=
  ∀ H : Subgroup X, H ≤ K → (∀ k ∈ K, (∀ s ∈ S, ⁅k, s⁆ ∈ kerAct W K S) → k ∈ H) →
    (∃ k ∈ H, ⁅k, a⁆ ∉ kerAct W K S) → K ≤ H

@[expose] def ThreeElt (W K S : Subgroup X) [W.Normal] (a : X) : Prop :=
  ∃ p ∈ K, p ^ 3 = 1 ∧ p ∉ kerAct W K S ∧ a * p * a⁻¹ * p ∈ kerAct W K S ∧
    ⁅p, a⁆ ∉ kerAct W K S ∧ p ∉ zPre W K

end CaseOneTwo

end CFSG.LocalAnalysis.GLTheoremB.Prop95Iv.I2810
