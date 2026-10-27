module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiCoordsAut
public import CFSG.LocalAnalysis.SeitzReduction.RankOneSuzukiStartBasic
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup CFSG.ABGLocalTools

section General

variable {G : Type*} [Group G]

theorem mem_normalizer_sup {H K : Subgroup G} {g : G} (hH : g ∈ normalizer (H : Set G))
    (hK : g ∈ normalizer (K : Set G)) : g ∈ normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  have key : ∀ g' ∈ normalizer (H : Set G) ⊓ normalizer (K : Set G), ∀ x ∈ H ⊔ K,
      g' * x * g'⁻¹ ∈ H ⊔ K := by
    intro g' hg' x hx
    have hle : H ⊔ K ≤ (H ⊔ K).comap (MulAut.conj g').toMonoidHom := by
      refine sup_le (fun y hy => mem_comap.mpr ?_) (fun y hy => mem_comap.mpr ?_)
      · have h1 : g' * y * g'⁻¹ ∈ H := (mem_normalizer_iff.mp (mem_inf.mp hg').1 y).mp hy
        simpa [MulAut.conj_apply] using (le_sup_left : H ≤ H ⊔ K) h1
      · have h1 : g' * y * g'⁻¹ ∈ K := (mem_normalizer_iff.mp (mem_inf.mp hg').2 y).mp hy
        simpa [MulAut.conj_apply] using (le_sup_right : K ≤ H ⊔ K) h1
    simpa [MulAut.conj_apply] using hle hx
  have hg : g ∈ normalizer (H : Set G) ⊓ normalizer (K : Set G) := mem_inf.mpr ⟨hH, hK⟩
  refine mem_normalizer_iff.mpr fun x => ⟨key g hg x, fun hx => ?_⟩
  have h1 := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using h1

theorem card_le_of_isPGroup_of_le [Finite G] {p : ℕ} [Fact p.Prime] {P H : Subgroup G}
    (hP : IsPGroup p P) (hPH : P ≤ H) : Nat.card P ≤ p ^ (Nat.card H).factorization p := by
  have hP' : IsPGroup p (P.subgroupOf H) := hP.of_equiv (subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  rw [← Nat.card_congr (subgroupOfEquivOfLe hPH).toEquiv, ← Sylow.card_eq_multiplicity Q]
  exact Subgroup.card_le_of_le hQ

theorem mem_map_conj_inv_iff {T : Subgroup G} {g y : G} :
    y ∈ T.map (MulAut.conj g⁻¹).toMonoidHom ↔ g * y * g⁻¹ ∈ T := by
  constructor
  · rintro ⟨z, hz, rfl⟩
    simpa [mul_assoc] using hz
  · intro hy
    exact ⟨g * y * g⁻¹, hy, by simp [mul_assoc]⟩

theorem exists_conj_eq_of_card_le [Finite G] {t g : G} {T P : Subgroup G}
    (hT : T ≤ centralizer ({t} : Set G))
    (hTc : Nat.card T = 2 ^ (Nat.card (centralizer ({t} : Set G))).factorization 2)
    (hP : P ≤ centralizer ({g⁻¹ * t * g} : Set G)) (hP2 : IsPGroup 2 P)
    (hcard : Nat.card T ≤ Nat.card P) :
    ∃ k : G, k⁻¹ * t * k = g⁻¹ * t * g ∧ ∀ y : G, y ∈ P ↔ k * y * k⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcH : Nat.card (centralizer ({g⁻¹ * t * g} : Set G)) =
      Nat.card (centralizer ({t} : Set G)) := card_centralizer_inv_mul_mul t g
  have hT'H : T.map (MulAut.conj g⁻¹).toMonoidHom ≤ centralizer ({g⁻¹ * t * g} : Set G) := by
    intro y hy
    have h1 := hT (mem_map_conj_inv_iff.mp hy)
    rw [← conj_mem_centralizer_conj_iff t g] at h1
    rwa [show g⁻¹ * (g * y * g⁻¹) * g = y by group] at h1
  have hcT' : Nat.card (T.map (MulAut.conj g⁻¹).toMonoidHom) = Nat.card T :=
    card_map_of_injective (MulAut.conj g⁻¹).injective
  have hsylT' : IsSylowOf 2 (T.map (MulAut.conj g⁻¹).toMonoidHom)
      (centralizer ({g⁻¹ * t * g} : Set G)) :=
    isSylowOf_of_card hT'H (by rw [hcT', hTc, hcH])
  have hle := card_le_of_isPGroup_of_le hP2 hP
  have hsylP : IsSylowOf 2 P (centralizer ({g⁻¹ * t * g} : Set G)) :=
    isSylowOf_of_card hP (le_antisymm hle (by rw [hcH, ← hTc]; exact hcard))
  obtain ⟨c, hcC, hc⟩ := hsylT'.exists_mem_conj hsylP
  refine ⟨g * c⁻¹, ?_, fun y => ?_⟩
  · have hcs : c * (g⁻¹ * t * g) = g⁻¹ * t * g * c := mem_centralizer_singleton_iff.mp hcC
    calc (g * c⁻¹)⁻¹ * t * (g * c⁻¹) = c * (g⁻¹ * t * g) * c⁻¹ := by group
      _ = g⁻¹ * t * g := by rw [hcs, mul_inv_cancel_right]
  · rw [hc y, mem_map_conj_inv_iff]
    constructor <;> intro hy <;> simpa [mul_assoc] using hy

theorem exists_mem_normalizer_inv_mul_mem_of_isSylowOf [Finite G] {p : ℕ} [Fact p.Prime]
    {R N : Subgroup G} (hR : IsSylowOf p R ⊤) (hRN : R ≤ normalizer (N : Set G))
    (hcomm : ∀ r ∈ R, ∀ r' ∈ R, r * r' * r⁻¹ * r'⁻¹ ∈ N) {t k : G} (ht : t ∈ R)
    (hk : k ∈ normalizer (N : Set G)) (hx : k⁻¹ * t * k ∈ R) :
    ∃ n ∈ normalizer (R : Set G), (k⁻¹ * t * k)⁻¹ * (n⁻¹ * t * n) ∈ N := by
  let C : Subgroup G :=
    { carrier := {y | y ∈ normalizer (N : Set G) ∧
        (k⁻¹ * t * k)⁻¹ * (y⁻¹ * (k⁻¹ * t * k) * y) ∈ N}
      mul_mem' := by
        rintro y y' ⟨hy, hyN⟩ ⟨hy', hy'N⟩
        refine ⟨mul_mem hy hy', ?_⟩
        have e : (k⁻¹ * t * k)⁻¹ * ((y * y')⁻¹ * (k⁻¹ * t * k) * (y * y')) =
            (k⁻¹ * t * k)⁻¹ * (y'⁻¹ * (k⁻¹ * t * k) * y') *
              (y'⁻¹ * ((k⁻¹ * t * k)⁻¹ * (y⁻¹ * (k⁻¹ * t * k) * y)) * y') := by group
        rw [e]
        exact mul_mem hy'N ((mem_normalizer_iff''.mp hy' _).mp hyN)
      one_mem' := ⟨one_mem _, by rw [inv_one, one_mul, mul_one, inv_mul_cancel]; exact one_mem _⟩
      inv_mem' := by
        rintro y ⟨hy, hyN⟩
        refine ⟨inv_mem hy, ?_⟩
        have e : (k⁻¹ * t * k)⁻¹ * (y⁻¹⁻¹ * (k⁻¹ * t * k) * y⁻¹) =
            (y * ((k⁻¹ * t * k)⁻¹ * (y⁻¹ * (k⁻¹ * t * k) * y)) * y⁻¹)⁻¹ := by group
        rw [e]
        exact inv_mem ((mem_normalizer_iff.mp hy _).mp hyN) }
  have hRC : R ≤ C := by
    intro r hr
    refine ⟨hRN hr, ?_⟩
    have h1 := hcomm _ (inv_mem hx) _ (inv_mem hr)
    have e : (k⁻¹ * t * k)⁻¹ * (r⁻¹ * (k⁻¹ * t * k) * r) =
        (k⁻¹ * t * k)⁻¹ * r⁻¹ * (k⁻¹ * t * k)⁻¹⁻¹ * r⁻¹⁻¹ := by group
    rw [e]
    exact h1
  have hRkC : R.map (MulAut.conj k⁻¹).toMonoidHom ≤ C := by
    intro y hy
    have hy' : k * y * k⁻¹ ∈ R := mem_map_conj_inv_iff.mp hy
    have hyr : y = k⁻¹ * (k * y * k⁻¹) * k := by group
    refine ⟨?_, ?_⟩
    · rw [hyr]
      exact mul_mem (mul_mem (inv_mem hk) (hRN hy')) hk
    · have e : (k⁻¹ * t * k)⁻¹ * (y⁻¹ * (k⁻¹ * t * k) * y) =
          k⁻¹ * (t⁻¹ * (k * y * k⁻¹)⁻¹ * t⁻¹⁻¹ * (k * y * k⁻¹)⁻¹⁻¹) * k := by group
      rw [e]
      exact (mem_normalizer_iff''.mp hk _).mp (hcomm _ (inv_mem ht) _ (inv_mem hy'))
  have hsylR : IsSylowOf p R C := hR.of_le hRC le_top
  have hcRk : Nat.card (R.map (MulAut.conj k⁻¹).toMonoidHom) = Nat.card R :=
    card_map_of_injective (MulAut.conj k⁻¹).injective
  have hsylRk : IsSylowOf p (R.map (MulAut.conj k⁻¹).toMonoidHom) C :=
    (isSylowOf_of_card le_top (by rw [hcRk, hR.card_eq])).of_le hRkC le_top
  obtain ⟨c, hcC, hc⟩ := hsylR.exists_mem_conj hsylRk
  obtain ⟨-, hcN⟩ := hcC
  refine ⟨k * c, mem_normalizer_iff''.mpr fun w => ?_, ?_⟩
  · have h1 := hc (k⁻¹ * w * k)
    rw [mem_map_conj_inv_iff, show k * (k⁻¹ * w * k) * k⁻¹ = w by group] at h1
    rw [h1]
    constructor <;> intro hw <;> simpa [mul_assoc] using hw
  · have e : (k * c)⁻¹ * t * (k * c) = c⁻¹ * (k⁻¹ * t * k) * c := by group
    rw [e]
    exact hcN

end General

section Coords

variable {G : Type*} [Group G] {K : Type*} [Field K] [Fintype K] [CharP K 2]
  {T₁ R₂ : Subgroup G} {t : G} {a : ℕ} {u v : G → K} {φ : G → K × K × K} {γ c : K}

variable (K) in
theorem card_szCoordSpace : Nat.card (szCoordSpace K) = 2 * Fintype.card K ^ 2 := by
  classical
  have h01 : (0 : K) ≠ 1 := zero_ne_one
  let e : szCoordSpace K ≃ K × K × Bool :=
    { toFun := fun z => ((z : K × K × K).1, (z : K × K × K).2.1, decide ((z : K × K × K).2.2 = 1))
      invFun := fun p => ⟨(p.1, p.2.1, if p.2.2 then 1 else 0), by
        rcases p with ⟨x, y, b⟩
        cases b
        · exact Or.inl rfl
        · exact Or.inr rfl⟩
      left_inv := fun z => by
        obtain ⟨⟨x, y, w⟩, hz⟩ := z
        rcases hz with h0 | h1
        · simp only at h0
          subst h0
          simp [h01]
        · simp only at h1
          subst h1
          simp
      right_inv := fun p => by
        rcases p with ⟨x, y, b⟩
        cases b <;> simp [h01] }
  rw [Nat.card_congr e, Nat.card_prod, Nat.card_prod, Nat.card_eq_fintype_card (α := Bool),
    Fintype.card_bool, Nat.card_eq_fintype_card]
  ring

namespace SzRCoords2

omit [Fintype K] in
theorem card_szR (h : SzRCoords2 T₁ R₂ t a u v φ γ c) :
    Nat.card (szR T₁ R₂ t) = Nat.card (szCoordSpace K) * Nat.card (szA₁ T₁) := by
  let Φ : szR T₁ R₂ t →* Multiplicative (szCoordSpace K) :=
    { toFun := fun x => Multiplicative.ofAdd ⟨φ x, h.mem x x.2⟩
      map_one' := by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
        congr 1
        exact Subtype.ext h.map_one
      map_mul' := fun x y => by
        rw [← ofAdd_add]
        congr 1
        exact Subtype.ext (h.mul _ x.2 _ y.2) }
  have hsurj : Function.Surjective Φ := by
    intro z
    obtain ⟨x, hx, hxz⟩ := h.surj _ (Multiplicative.toAdd z).2
    refine ⟨⟨x, hx⟩, ?_⟩
    show Multiplicative.ofAdd _ = z
    rw [← ofAdd_toAdd z]
    congr 1
    exact Subtype.ext hxz
  have hker : Φ.ker = (szA₁ T₁).subgroupOf (szR T₁ R₂ t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, ← h.ker x x.2]
    constructor
    · intro hx
      have h1 := congrArg (fun z => ((Multiplicative.toAdd z : szCoordSpace K) : K × K × K)) hx
      simpa [Φ] using h1
    · intro hx
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
      congr 1
      exact Subtype.ext hx
  have h1 := Subgroup.card_mul_index Φ.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, hker,
    Nat.card_congr (subgroupOfEquivOfLe ((szA₁_le T₁).trans (le_szR_left T₁ R₂ t))).toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (szCoordSpace K) ≃ _)] at h1
  rw [← h1, mul_comm]

theorem card_szR_le_mul (h : SzRCoords2 T₁ R₂ t a u v φ γ c) {x : G} (hx : x ∈ szR T₁ R₂ t) :
    Nat.card (szR T₁ R₂ t) ≤
      Fintype.card K * Nat.card (szR T₁ R₂ t ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  let ψ : szR T₁ R₂ t →* Multiplicative K :=
    { toFun := fun w => Multiplicative.ofAdd (v ((w : G) * x * (w : G)⁻¹ * x⁻¹))
      map_one' := by
        show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
        rw [OneMemClass.coe_one, one_mul, inv_one, mul_one, mul_inv_cancel, h.v_one]
      map_mul' := fun w w' => by
        rw [← ofAdd_add]
        congr 1
        rw [Subgroup.coe_mul, h.comm _ (mul_mem w.2 w'.2) x hx, h.comm _ w.2 x hx,
          h.comm _ w'.2 x hx, h.mul _ w.2 _ w'.2, szCommMap_add_left] }
  have hker : ψ.ker = (szR T₁ R₂ t ⊓ centralizer ({x} : Set G)).subgroupOf (szR T₁ R₂ t) := by
    ext w
    rw [MonoidHom.mem_ker, mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · intro hw
      have h0 : v ((w : G) * x * (w : G)⁻¹ * x⁻¹) = 0 := by
        have h1 := congrArg Multiplicative.toAdd hw
        simpa [ψ] using h1
      have h1 := h.v_inj _ (h.comm_mem _ w.2 x hx) h0
      refine ⟨w.2, ?_⟩
      calc (w : G) * x = (w : G) * x * (w : G)⁻¹ * x⁻¹ * (x * w) := by group
        _ = x * w := by rw [h1, one_mul]
    · rintro ⟨-, hw⟩
      show Multiplicative.ofAdd _ = Multiplicative.ofAdd 0
      rw [hw, mul_inv_cancel_right, mul_inv_cancel, h.v_one]
  have h1 := Subgroup.card_mul_index ψ.ker
  rw [Subgroup.index_ker, hker, Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv] at h1
  have hrange : Nat.card ψ.range ≤ Fintype.card K := by
    calc Nat.card ψ.range ≤ Nat.card (Multiplicative K) := Subgroup.card_le_card_group _
      _ = Fintype.card K := by
        rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative K ≃ K), Nat.card_eq_fintype_card]
  calc Nat.card (szR T₁ R₂ t) = Nat.card ψ.range *
        Nat.card (szR T₁ R₂ t ⊓ centralizer ({x} : Set G) : Subgroup G) := by rw [← h1, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_right _ hrange

end SzRCoords2

end Coords

end CFSG.SeitzReduction.RankOne
