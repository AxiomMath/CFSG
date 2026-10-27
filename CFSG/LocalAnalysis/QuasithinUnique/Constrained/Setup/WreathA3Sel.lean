module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellNatActual
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerParab2
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.QuasithinUnique.Setup.Wreath

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.Campbell
  CFSG.Quasithin.BlueprintB2
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

structure A3SelHyp (X T N R P : Subgroup G) : Prop where
  T_sylow : IsSylowTwoOf T X
  N_le : N ≤ X
  N_norm : X ≤ normalizer (N : Set G)
  X_eq : N ⊔ T = X
  N_noTwo : NoPQuotient 2 ↥N
  R_le_T : R ≤ T
  T_norm_R : T ≤ normalizer (R : Set G)
  R_sylow : IsSylowTwoOf R (N ⊔ R)
  charTwo : CharTwo (N ⊔ R)
  R_le_P : R ≤ P
  P_le : P ≤ N ⊔ R
  X_eq_P : P ⊔ T = X
  R_not_normal : ¬ P ≤ normalizer (R : Set G)
  max : ∃ K : Subgroup G, R ≤ K ∧ K < P ∧ ∀ Y : Subgroup G, R ≤ Y → Y < P → Y ≤ K
  noChar : NoCharNormal R P

theorem slPerm_apply_mulVec (A : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (w : Fin 2 → ZMod 2) :
    slPerm (ZMod 2) A w = (A : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec w := by
  rw [slPerm_apply, Matrix.SpecialLinearGroup.smul_def]
  rfl

omit [Finite G] in
theorem oddOrderSubgroup_top_map (P : Subgroup G) :
    (oddOrderSubgroup (⊤ : Subgroup ↥P)).map P.subtype = oddOrderSubgroup P := by
  unfold oddOrderSubgroup
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨y, ⟨-, hy⟩, rfl⟩
    exact ⟨y.2, by simpa [Subgroup.orderOf_coe] using hy⟩
  · rintro ⟨hx, hodd⟩
    exact ⟨⟨x, hx⟩, ⟨trivial, by simpa [Subgroup.orderOf_coe] using hodd⟩, rfl⟩

theorem elemThompsonIn_subgroupOf_map_eq {R P : Subgroup G} (hRP : R ≤ P) :
    (elemThompsonIn 2 (R.subgroupOf P)).map P.subtype = CFSG.Quasithin.thompsonJ R := by
  rw [← elemThompsonIn_map_of_injective 2 P.subtype P.subtype_injective,
    Subgroup.map_subgroupOf_eq_of_le hRP]
  exact CFSG.Quasithin.elemThompson_map_subtype_eq_thompsonJ R


theorem characteristic_map_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    {K : Subgroup A} (hK : K.Characteristic) : (K.map e.toMonoidHom).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro φ
  have hψ := Subgroup.characteristic_iff_map_eq.mp hK (e.trans (φ.trans e.symm))
  rw [Subgroup.map_map]
  have : φ.toMonoidHom.comp e.toMonoidHom =
      e.toMonoidHom.comp (e.trans (φ.trans e.symm)).toMonoidHom := by
    ext x
    simp
  rw [this, ← Subgroup.map_map, hψ]

namespace A3SelHyp

variable {X T N R P : Subgroup G} (h : A3SelHyp X T N R P)

include h

omit [Finite G] in
theorem R_sylow_P : IsSylowTwoOf R P := by
  refine ⟨h.R_le_P, h.R_sylow.2.1, ?_⟩
  intro h2
  apply h.R_sylow.2.2
  have h1 : R.relIndex P * P.relIndex (N ⊔ R) = R.relIndex (N ⊔ R) :=
    Subgroup.relIndex_mul_relIndex R P (N ⊔ R) h.R_le_P h.P_le
  show 2 ∣ R.relIndex (N ⊔ R)
  rw [← h1]
  exact Dvd.dvd.mul_right h2 _

omit [Finite G] in
theorem Q_le_P : blockQ (N ⊔ R) ≤ P := h.R_sylow.pCoreOf_le.trans h.R_le_P

theorem charTwo_top : CharTwo (⊤ : Subgroup ↥P) := by
  intro x hx
  rw [CFSG.Quasithin.B6.pCoreOf_top] at hx ⊢
  have hQP := h.Q_le_P
  have hQn : (blockQ (N ⊔ R)).subgroupOf P |>.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQP).2
      (h.P_le.trans (C1.le_normalizer_blockQ _))
  have hQ2 : IsPGroup 2 ((blockQ (N ⊔ R)).subgroupOf P) :=
    (C1.blockQ_isPGroup _).of_equiv (Subgroup.subgroupOfEquivOfLe hQP).symm
  have hle : (blockQ (N ⊔ R)).subgroupOf P ≤ CFSG.Open.pCore 2 ↥P := CFSG.LieType.BorelTits.le_pCore 2 hQn hQ2
  have hxc : x.1 ∈ Subgroup.centralizer ((blockQ (N ⊔ R) : Subgroup G) : Set G) := by
    exact (mem_centralizer_subgroupOf_iff hQP x).1
      (Subgroup.centralizer_le (by exact_mod_cast hle) hx.2)
  have hxQ : (x : G) ∈ blockQ (N ⊔ R) :=
    h.charTwo ⟨h.P_le x.2, hxc⟩
  exact hle (Subgroup.mem_subgroupOf.2 hxQ)


omit [Finite G] in
theorem noCharNormal_top : NoCharNormal (R.subgroupOf P) (⊤ : Subgroup ↥P) := by
  intro C' hC'R hC'ne hC'char hn
  have hRP := h.R_le_P
  set C : Subgroup G := C'.map P.subtype with hC
  have hCR : C ≤ R := by
    have := Subgroup.map_mono (f := P.subtype) hC'R
    rwa [Subgroup.map_subgroupOf_eq_of_le hRP] at this
  have hCP : C ≤ P := hCR.trans hRP
  have hCne : C ≠ ⊥ := by
    intro hb
    exact hC'ne ((Subgroup.map_eq_bot_iff_of_injective _ P.subtype_injective).1 hb)
  have hCsub : C.subgroupOf P = C' := Subgroup.comap_map_eq_self_of_injective P.subtype_injective C'
  have hchar : (C.subgroupOf R).Characteristic := by
    let e : ↥(R.subgroupOf P) ≃* ↥R := Subgroup.subgroupOfEquivOfLe hRP
    have h1 := characteristic_map_mulEquiv e hC'char
    have h2 : (C'.subgroupOf (R.subgroupOf P)).map e.toMonoidHom = C.subgroupOf R := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        have hy' : (y : ↥P) ∈ C' := hy
        exact ⟨y, hy', rfl⟩
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hx
        refine ⟨⟨⟨x, hRP x.2⟩, ?_⟩, ?_, ?_⟩
        · exact Subgroup.mem_subgroupOf.mpr x.2
        · show (⟨(x : G), hRP x.2⟩ : ↥P) ∈ C'
          have : (⟨(x : G), hRP x.2⟩ : ↥P) = y := Subtype.ext hyx.symm
          rw [this]
          exact hy
        · rfl
    rw [← h2]
    exact h1
  have hnor : C'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hn)
  refine h.noChar C hCR hCne hchar ?_
  rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hCP, hCsub]
  exact hnor


omit [Finite G] in
theorem natQuotSetting {V : Subgroup G} (hV : CFSG.Quasithin.IsTwoReducedIn P V)
    (ρ : ↥P →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) (hρ : Function.Surjective ρ)
    (ψ : ↥V →* Multiplicative (Fin 2 → ZMod 2)) (hψ : Function.Surjective ψ)
    (hψρ : ∀ (p : ↥P) (v v' : ↥V), (v' : G) = (p : G) * (v : G) * (p : G)⁻¹ →
      Multiplicative.toAdd (ψ v') =
        (ρ p : Matrix (Fin 2) (Fin 2) (ZMod 2)).mulVec (Multiplicative.toAdd (ψ v)))
    (hψker : ψ.ker = (Subgroup.centralizer (oddOrderSubgroup P : Set G)).subgroupOf V) :
    ∃ (K : Subgroup ↥P) (ρ' : ↥P →* Gamma (ZMod 2))
      (φ : ↥(V.subgroupOf P) →* Multiplicative (Fin 2 → ZMod 2)),
      IsNatQuotSetting (R.subgroupOf P) K (V.subgroupOf P) ρ' φ := by
  classical
  have hRP := h.R_le_P
  have hVP : V ≤ P := hV.1
  obtain ⟨K0, hRK, hKP, hK⟩ := h.max
  let ρ' : ↥P →* Gamma (ZMod 2) :=
    ((slGamma (ZMod 2)).subtype.comp (slGammaEquiv (ZMod 2)).toMonoidHom).comp ρ
  have hρ'apply : ∀ p : ↥P, ((ρ' p : Gamma (ZMod 2)) : Equiv.Perm (Fin 2 → ZMod 2)) =
      slPerm (ZMod 2) (ρ p) := fun p => rfl
  let e : ↥(V.subgroupOf P) ≃* ↥V := Subgroup.subgroupOfEquivOfLe hVP
  let φ : ↥(V.subgroupOf P) →* Multiplicative (Fin 2 → ZMod 2) := ψ.comp e.toMonoidHom
  have hVn : (V.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVP).2 hV.2.1
  refine ⟨K0.subgroupOf P, ρ', φ, ?_⟩
  refine
    { sylow := Layer.isSylowTwoOf_subgroupOf_top' h.R_sylow_P
      nonnormal := fun hn => h.R_not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hRP).mp hn)
      le_M := fun x hx => Subgroup.mem_subgroupOf.mpr (hRK (Subgroup.mem_subgroupOf.mp hx))
      M_lt := ?_
      M_max := ?_
      reduced := ?_
      sl_le := ?_
      two_quot := ?_
      φ_surj := hψ.comp e.surjective
      φ_equiv := ?_
      φ_ker := ?_ }
  · refine lt_top_iff_ne_top.mpr fun htop => ?_
    have hPK : P ≤ K0 := fun x hx =>
      Subgroup.mem_subgroupOf.mp (show (⟨x, hx⟩ : ↥P) ∈ K0.subgroupOf P by rw [htop]; trivial)
    exact absurd hPK (not_le_of_gt hKP)
  · intro Y hRY hY
    have hRY' : R ≤ Y.map P.subtype := by
      have := Subgroup.map_mono (f := P.subtype) hRY
      rwa [Subgroup.map_subgroupOf_eq_of_le hRP] at this
    have hYP : Y.map P.subtype < P := by
      refine lt_of_le_of_ne (map_subtype_le_self Y) fun heq => ?_
      apply (lt_top_iff_ne_top.mp hY)
      refine top_unique fun x _ => ?_
      have hx : (x : G) ∈ Y.map P.subtype := by rw [heq]; exact x.2
      obtain ⟨y, hy, hyx⟩ := hx
      have : y = x := Subtype.ext hyx
      rwa [this] at hy
    intro y hy
    exact Subgroup.mem_subgroupOf.mpr (hK _ hRY' hYP ⟨y, hy, rfl⟩)
  · refine ⟨le_top, top_le_iff.mpr (Subgroup.normalizer_eq_top_iff.mpr hVn), ?_, ?_⟩
    · have hel := hV.2.2.1
      have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb => by
        have := hel.1
        exact setLike_mul_comm ha hb
      refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => Subtype.ext ?_⟩
      · exact hcomm _ (Subgroup.mem_subgroupOf.mp a.2) _ (Subgroup.mem_subgroupOf.mp b.2)
      · have := hel.2 _ (Subgroup.mem_subgroupOf.mp hx)
        simpa using this
    · intro D' _ hDn hDpow
      have hDnormal : D'.Normal := Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp hDn)
      have hD₀P : D'.map P.subtype ≤ P := map_subtype_le_self D'
      have hD₀N : P ≤ normalizer ((D'.map P.subtype : Subgroup G) : Set G) := by
        rw [← Subgroup.normal_subgroupOf_iff_le_normalizer hD₀P, subgroupOf_map_subtype_self]
        exact hDnormal
      have hres := hV.2.2.2 (D'.map P.subtype) hD₀P hD₀N (by
        rintro _ ⟨d, hd, rfl⟩
        obtain ⟨k, hk⟩ := hDpow d hd
        refine ⟨k, ?_⟩
        have := (mem_centralizer_subgroupOf_iff hVP (d ^ 2 ^ k)).mp hk
        simpa using this)
      intro d hd
      exact (mem_centralizer_subgroupOf_iff hVP d).mpr (hres ⟨d, hd, rfl⟩)
  · intro A
    obtain ⟨p, hp⟩ := hρ A
    exact ⟨p, by rw [hρ'apply, hp]⟩
  · intro p
    exact ⟨0, by rw [pow_zero, pow_one]; exact (slGammaEquiv (ZMod 2) (ρ p)).2⟩
  · intro p v v' hv'
    have h1 := hψρ p (e v) (e v') (by exact congrArg Subtype.val hv')
    rw [hρ'apply, slPerm_apply_mulVec]
    exact h1
  · ext v
    have hL : (oddOrderSubgroup (⊤ : Subgroup ↥P)) = (oddOrderSubgroup P).subgroupOf P := by
      rw [← oddOrderSubgroup_top_map P]
      exact (Subgroup.comap_map_eq_self_of_injective P.subtype_injective _).symm
    rw [hL, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : e v ∈ ψ.ker := hv
      rw [hψker, Subgroup.mem_subgroupOf] at h1
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mpr h1
    · intro hv
      show e v ∈ ψ.ker
      rw [hψker, Subgroup.mem_subgroupOf]
      exact (mem_centralizer_subgroupOf_iff (oddOrderSubgroup_le P) (v : ↥P)).mp hv

end A3SelHyp

end CFSG.QuasithinUnique.Setup.Wreath
