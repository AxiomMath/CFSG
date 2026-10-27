module

public import CFSG.CGT.PushingUpLit.A78L3.Side

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.QuasithinUnique.Setup.Offender (IsSemilinearWith)
open CFSG.QuasithinUnique.Setup.Campbell (slPerm)
open Matrix

structure NatCoordK (G : Type) [Group G] (L V K : Subgroup G) (F : Type) [Field F] where
  κ : G → Fin 2 → F
  ρ : G → SpecialLinearGroup (Fin 2) F
  K_le : K ≤ V
  κ_mul : ∀ v ∈ V, ∀ w ∈ V, κ (v * w) = κ v + κ w
  κ_eq_zero : ∀ v ∈ V, κ v = 0 ↔ v ∈ K
  κ_surj : ∀ x : Fin 2 → F, ∃ v ∈ V, κ v = x
  ρ_mul : ∀ l ∈ L, ∀ m ∈ L, ρ (l * m) = ρ l * ρ m
  ρ_surj : ∀ g : SpecialLinearGroup (Fin 2) F, ∃ l ∈ L, ρ l = g
  ρ_eq_one : ∀ l ∈ L, ρ l = 1 ↔ l ∈ V
  norm : ∀ l ∈ L, ∀ v ∈ V, l * v * l⁻¹ ∈ V
  conj : ∀ l ∈ L, ∀ v ∈ V, κ (l * v * l⁻¹) = (ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ κ v

section Construction

variable {G : Type} [Group G] {e : ℕ}

theorem nonempty_natCoordK_of_isNatSL {E V K : Subgroup G} (hnat : BHS.IsNatSL E V e)
    (hK : V ⊓ Subgroup.centralizer (E : Set G) = K)
    (hCL : E ⊓ Subgroup.centralizer (V : Set G) = E ⊓ V)
    (hnorm : ∀ l ∈ E, ∀ v ∈ V, l * v * l⁻¹ ∈ V) :
    Nonempty (NatCoordK G E V K (GaloisField 2 e)) := by
  classical
  obtain ⟨φ, ψ, hs, hk, hψs, hψk, hψc⟩ := hnat
  let κ : G → Fin 2 → GaloisField 2 e := fun g =>
    if hg : g ∈ V then Multiplicative.toAdd (ψ ⟨g, hg⟩) else 0
  let ρ : G → SpecialLinearGroup (Fin 2) (GaloisField 2 e) := fun g =>
    if hg : g ∈ E then φ ⟨g, hg⟩ else 1
  have hκ : ∀ (g : G) (hg : g ∈ V), κ g = Multiplicative.toAdd (ψ ⟨g, hg⟩) := fun g hg => by
    simp only [κ, hg, ↓reduceDIte]
  have hρ : ∀ (g : G) (hg : g ∈ E), ρ g = φ ⟨g, hg⟩ := fun g hg => by
    simp only [ρ, hg, ↓reduceDIte]
  refine ⟨{
    κ := κ
    ρ := ρ
    K_le := hK ▸ inf_le_left
    κ_mul := ?_
    κ_eq_zero := ?_
    κ_surj := ?_
    ρ_mul := ?_
    ρ_surj := ?_
    ρ_eq_one := ?_
    norm := hnorm
    conj := ?_ }⟩
  · intro v hv w hw
    rw [hκ v hv, hκ w hw, hκ _ (mul_mem hv hw)]
    rw [show (⟨v * w, mul_mem hv hw⟩ : ↥V) = ⟨v, hv⟩ * ⟨w, hw⟩ from rfl, map_mul, toAdd_mul]
  · intro v hv
    rw [hκ v hv]
    constructor
    · intro h0
      have h1 : ψ ⟨v, hv⟩ = 1 := Multiplicative.toAdd.injective (by rw [h0]; rfl)
      have h2 : (⟨v, hv⟩ : ↥V) ∈ ψ.ker := h1
      rw [hψk, Subgroup.mem_subgroupOf, hK] at h2
      exact h2
    · intro hvK
      have h2 : (⟨v, hv⟩ : ↥V) ∈ ψ.ker := by
        rw [hψk, Subgroup.mem_subgroupOf, hK]
        exact hvK
      rw [MonoidHom.mem_ker.1 h2]
      rfl
  · intro x
    obtain ⟨⟨v, hv⟩, hvx⟩ := hψs (Multiplicative.ofAdd x)
    exact ⟨v, hv, by rw [hκ v hv, hvx, toAdd_ofAdd]⟩
  · intro l hl m hm
    rw [hρ l hl, hρ m hm, hρ _ (mul_mem hl hm), ← map_mul]
    rfl
  · intro g
    obtain ⟨⟨l, hl⟩, hlg⟩ := hs g
    exact ⟨l, hl, by rw [hρ l hl, hlg]⟩
  · intro l hl
    rw [hρ l hl]
    constructor
    · intro h1
      have h2 : (⟨l, hl⟩ : ↥E) ∈ φ.ker := h1
      rw [hk, Subgroup.mem_subgroupOf, hCL] at h2
      exact h2.2
    · intro hlV
      have h3 : (⟨l, hl⟩ : ↥E) ∈ φ.ker := by
        rw [hk, Subgroup.mem_subgroupOf, hCL]
        exact ⟨hl, hlV⟩
      exact h3
  · intro l hl v hv
    rw [hκ _ (hnorm l hl v hv), hκ v hv, hρ l hl, hψc ⟨l, hl⟩ ⟨v, hv⟩ (hnorm l hl v hv),
      toAdd_ofAdd]

theorem _root_.CFSG.CGT.PushingUpLit.A78.A78Side.nonempty_natCoordK [Finite G]
    {L T J : Subgroup G} (h : A78Side G L T J e) :
    Nonempty (NatCoordK G (L ⊔ oTwoIn (L ⊔ T)) (oTwoIn (L ⊔ T))
      (oTwoIn (L ⊔ T) ⊓ Subgroup.centralizer (L : Set G)) (GaloisField 2 e)) :=
  nonempty_natCoordK_of_isNatSL h.isNatSL_sup h.inf_centralizer_sup_V
    (h.sup_inf_centralizer_V.trans (inf_eq_right.2 le_sup_right).symm)
    (fun _ hl _ hv => h.conj_V (sup_le le_sup_left (h.V_le_T.trans le_sup_right) hl) hv)

end Construction

namespace NatCoordK

variable {G : Type} [Group G] {L V K : Subgroup G} {F : Type} [Field F] (D : NatCoordK G L V K F)

theorem ρ_mulVec_mul {l m : G} (hl : l ∈ L) (hm : m ∈ L) (u : Fin 2 → F) :
    (D.ρ (l * m) : Matrix (Fin 2) (Fin 2) F) *ᵥ u =
      (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ ((D.ρ m : Matrix (Fin 2) (Fin 2) F) *ᵥ u) := by
  simp only [coe_mulVec_eq_smul]
  rw [D.ρ_mul l hl m hm, mul_smul]

theorem ρ_mulVec_of_mem {v : G} (hvL : v ∈ L) (hv : v ∈ V) (u : Fin 2 → F) :
    (D.ρ v : Matrix (Fin 2) (Fin 2) F) *ᵥ u = u := by
  simp only [coe_mulVec_eq_smul]
  rw [(D.ρ_eq_one v hvL).2 hv, one_smul]

theorem κ_one : D.κ 1 = 0 := (D.κ_eq_zero 1 V.one_mem).2 K.one_mem

theorem κ_inv {v : G} (hv : v ∈ V) : D.κ v⁻¹ = -D.κ v := by
  have h := D.κ_mul v hv v⁻¹ (inv_mem hv)
  rw [mul_inv_cancel, D.κ_one] at h
  exact (neg_eq_of_add_eq_zero_right h.symm).symm

theorem κ_of_mem_K {k : G} (hk : k ∈ K) : D.κ k = 0 := (D.κ_eq_zero k (D.K_le hk)).2 hk

theorem κ_ne_zero {v : G} (hv : v ∈ V) (hvK : v ∉ K) : D.κ v ≠ 0 := fun h0 =>
  hvK ((D.κ_eq_zero v hv).1 h0)

theorem κ_eq_iff {v w : G} (hv : v ∈ V) (hw : w ∈ V) : D.κ v = D.κ w ↔ v * w⁻¹ ∈ K := by
  rw [← D.κ_eq_zero _ (mul_mem hv (inv_mem hw)), D.κ_mul _ hv _ (inv_mem hw), D.κ_inv hw,
    ← sub_eq_add_neg, sub_eq_zero]

theorem ρ_one : D.ρ 1 = 1 := by
  have h := D.ρ_mul 1 L.one_mem 1 L.one_mem
  rw [one_mul] at h
  have h2 : D.ρ 1 * D.ρ 1 = D.ρ 1 * 1 := by rw [← h, mul_one]
  exact mul_left_cancel h2

theorem ρ_inv {l : G} (hl : l ∈ L) : D.ρ l⁻¹ = (D.ρ l)⁻¹ := by
  have h := D.ρ_mul l hl l⁻¹ (inv_mem hl)
  rw [mul_inv_cancel, D.ρ_one] at h
  exact (eq_inv_of_mul_eq_one_right h.symm)

@[expose] noncomputable def toHom : ↥V →* Multiplicative (Fin 2 → F) where
  toFun v := Multiplicative.ofAdd (D.κ v)
  map_one' := by simp [D.κ_one]
  map_mul' v w := by
    show Multiplicative.ofAdd (D.κ ((v : G) * w)) = _
    rw [D.κ_mul _ v.2 _ w.2, ofAdd_add]

theorem toHom_ker : D.toHom.ker = K.subgroupOf V := by
  ext v
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← D.κ_eq_zero _ v.2]
  show Multiplicative.ofAdd (D.κ v) = 1 ↔ _
  rw [← ofAdd_zero]
  exact Multiplicative.ofAdd.injective.eq_iff

theorem toHom_surjective : Function.Surjective D.toHom := by
  intro x
  obtain ⟨v, hv, hvx⟩ := D.κ_surj (Multiplicative.toAdd x)
  exact ⟨⟨v, hv⟩, by show Multiplicative.ofAdd (D.κ v) = x; rw [hvx]; rfl⟩

include D in
theorem card_V [Finite G] : Nat.card V = Nat.card F ^ 2 * Nat.card K := by
  have h1 := Subgroup.card_ker_mul_card_range D.toHom
  rw [MonoidHom.range_eq_top.2 D.toHom_surjective, Subgroup.card_top, D.toHom_ker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe D.K_le).toEquiv,
    Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 2),
    Fintype.card_fin] at h1
  rw [← h1, mul_comm]

theorem κ_comm {w l : G} (hw : w ∈ V) (hl : l ∈ L) :
    D.κ (w * (l * w⁻¹ * l⁻¹)) =
      D.κ w - (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.κ w := by
  rw [D.κ_mul w hw _ (D.norm l hl _ (inv_mem hw)), D.conj l hl _ (inv_mem hw), D.κ_inv hw,
    mulVec_neg, sub_eq_add_neg]

include D in
theorem le_normalizer : L ≤ Subgroup.normalizer (V : Set G) :=
  le_normalizer_of_conj D.norm

include D in
theorem le_normalizer_K : L ≤ Subgroup.normalizer (K : Set G) := by
  refine le_normalizer_of_conj fun l hl k hk => ?_
  have hkV := D.K_le hk
  refine (D.κ_eq_zero _ (D.norm l hl k hkV)).1 ?_
  rw [D.conj l hl k hkV, D.κ_of_mem_K hk, mulVec_zero]

include D in
theorem le_normVK : L ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G) :=
  le_inf D.le_normalizer D.le_normalizer_K

@[expose] noncomputable def sec (w : Fin 2 → F) : G := (D.κ_surj w).choose

theorem sec_mem (w : Fin 2 → F) : D.sec w ∈ V := (D.κ_surj w).choose_spec.1

theorem κ_sec (w : Fin 2 → F) : D.κ (D.sec w) = w := (D.κ_surj w).choose_spec.2

@[expose] noncomputable def act (x : G) (w : Fin 2 → F) : Fin 2 → F := D.κ (x * D.sec w * x⁻¹)

variable {D}

theorem κ_conj_congr {x v v' : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (hv : v ∈ V) (hv' : v' ∈ V) (h : D.κ v = D.κ v') :
    D.κ (x * v * x⁻¹) = D.κ (x * v' * x⁻¹) := by
  rw [D.κ_eq_iff hv hv'] at h
  rw [D.κ_eq_iff (conj_mem_of_mem_normalizer hx.1 hv) (conj_mem_of_mem_normalizer hx.1 hv')]
  have e : x * v * x⁻¹ * (x * v' * x⁻¹)⁻¹ = x * (v * v'⁻¹) * x⁻¹ := by group
  rw [e]
  exact conj_mem_of_mem_normalizer hx.2 h

theorem act_κ {x v : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) (hv : v ∈ V) :
    D.act x (D.κ v) = D.κ (x * v * x⁻¹) :=
  κ_conj_congr hx (D.sec_mem _) hv (D.κ_sec _)

theorem act_add {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (w w' : Fin 2 → F) : D.act x (w + w') = D.act x w + D.act x w' := by
  have hs : w + w' = D.κ (D.sec w * D.sec w') := by
    rw [D.κ_mul _ (D.sec_mem w) _ (D.sec_mem w'), D.κ_sec, D.κ_sec]
  have e : x * (D.sec w * D.sec w') * x⁻¹ = (x * D.sec w * x⁻¹) * (x * D.sec w' * x⁻¹) := by
    group
  rw [hs, act_κ hx (mul_mem (D.sec_mem w) (D.sec_mem w')), e,
    D.κ_mul _ (conj_mem_of_mem_normalizer hx.1 (D.sec_mem w)) _
      (conj_mem_of_mem_normalizer hx.1 (D.sec_mem w'))]
  rfl

theorem act_mul {x y : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (w : Fin 2 → F) : D.act (x * y) w = D.act x (D.act y w) := by
  conv_lhs => rw [← D.κ_sec w]
  conv_rhs => rw [← D.κ_sec w]
  rw [act_κ (mul_mem hx hy) (D.sec_mem w), act_κ hy (D.sec_mem w),
    act_κ hx (conj_mem_of_mem_normalizer hy.1 (D.sec_mem w))]
  congr 1
  group

theorem act_one (w : Fin 2 → F) : D.act 1 w = w := by
  rw [act, one_mul, inv_one, mul_one, D.κ_sec]

theorem act_of_mem_L {l : G} (hl : l ∈ L) (w : Fin 2 → F) :
    D.act l w = (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w := by
  rw [act, D.conj l hl _ (D.sec_mem w), D.κ_sec]

theorem act_inv_act {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (w : Fin 2 → F) : D.act x⁻¹ (D.act x w) = w := by
  rw [← act_mul (inv_mem hx) hx, inv_mul_cancel, act_one]

theorem act_act_inv {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (w : Fin 2 → F) : D.act x (D.act x⁻¹ w) = w := by
  rw [← act_mul hx (inv_mem hx), mul_inv_cancel, act_one]

variable (D) in
@[expose] noncomputable def actPerm (x : G)
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) :
    Equiv.Perm (Fin 2 → F) where
  toFun := D.act x
  invFun := D.act x⁻¹
  left_inv w := act_inv_act hx w
  right_inv w := act_act_inv hx w

theorem actPerm_apply {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (w : Fin 2 → F) : D.actPerm x hx w = D.act x w := rfl

theorem act_twist {x l : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) (hl : l ∈ L)
    (w : Fin 2 → F) :
    D.act x ((D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ w) =
      (D.ρ (x * l * x⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ D.act x w := by
  have hxl : x * l * x⁻¹ ∈ L := conj_mem_of_mem_normalizer hxL hl
  rw [← act_of_mem_L hl, ← act_of_mem_L hxl, ← act_mul hx (D.le_normVK hl),
    ← act_mul (D.le_normVK hxl) hx]
  congr 1
  group

theorem exists_semilinear [Finite F] {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G)) :
    ∃ σ : F ≃+* F, IsSemilinearWith (D.actPerm x hx) σ := by
  refine BHS.exists_isSemilinearWith_of_normalizes (D.actPerm x hx)
    (fun w w' => act_add hx w w') fun g => ?_
  obtain ⟨l, hl, rfl⟩ := D.ρ_surj g
  have hxl : x⁻¹ * l * x⁻¹⁻¹ ∈ L := conj_mem_of_mem_normalizer (inv_mem hxL) hl
  refine ⟨D.ρ (x⁻¹ * l * x⁻¹⁻¹), Equiv.ext fun w => ?_⟩
  show D.act x⁻¹ ((D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.act x w) =
    (D.ρ (x⁻¹ * l * x⁻¹⁻¹) : Matrix (Fin 2) (Fin 2) F) *ᵥ w
  rw [act_twist (inv_mem hxL) (inv_mem hx) hl, act_inv_act hx]

theorem act_of_mem_centralizer {x : G} (hx : x ∈ Subgroup.centralizer (V : Set G))
    (w : Fin 2 → F) : D.act x w = w := by
  rw [act]
  have h1 := Subgroup.mem_centralizer_iff.1 hx _ (D.sec_mem w)
  rw [show x * D.sec w * x⁻¹ = D.sec w by rw [← h1]; group, D.κ_sec]

theorem comm_mem_of_act {x : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (K : Set G))
    (h : ∀ w, D.act x w = w) {v : G} (hv : v ∈ V) : x * v * x⁻¹ * v⁻¹ ∈ K := by
  have h1 := h (D.κ v)
  rw [act_κ hx hv] at h1
  exact (D.κ_eq_iff (conj_mem_of_mem_normalizer hx.1 hv) hv).1 h1

include D in
theorem exists_conj {v w : G} (hv : v ∈ V) (hvK : v ∉ K) (hw : w ∈ V) (hwK : w ∉ K) :
    ∃ l ∈ L, D.κ (l * v * l⁻¹) = D.κ w := by
  obtain ⟨M, -, hM⟩ := exists_fixSL_mulVec_eq (σ := RingEquiv.refl F) (D.κ_ne_zero hv hvK)
    (D.κ_ne_zero hw hwK) (fun _ => rfl) (fun _ => rfl)
  obtain ⟨l, hl, hlM⟩ := D.ρ_surj M
  refine ⟨l, hl, ?_⟩
  rw [D.conj l hl v hv, hlM]
  exact hM

end NatCoordK

namespace NatCoordK

variable {G : Type} [Group G] {L V K : Subgroup G} {F : Type} [Field F] [CharP F 2]
  (D : NatCoordK G L V K F)

include D in
theorem sq_mem_of_fix {v l : G} (hv : v ∈ V) (hvK : v ∉ K) (hl : l ∈ L)
    (hfix : (D.ρ l : Matrix (Fin 2) (Fin 2) F) *ᵥ D.κ v = D.κ v) : l * l ∈ V := by
  have := sq_eq_one_of_mulVec_eq (D.κ_ne_zero hv hvK) hfix
  rw [← D.ρ_mul l hl l hl] at this
  exact (D.ρ_eq_one _ (mul_mem hl hl)).1 this

end NatCoordK

end CFSG.CGT.PushingUpLit.A78S4
