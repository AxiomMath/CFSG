module

public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveOmeLeviData
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveSylLang

public section

namespace CFSG.SeitzReduction.LinearPilot

open Subgroup CFSG.Blueprint CFSG.LocalAnalysis.ComponentInitial LinearFlag Matrix

@[expose] def LFiveWOneFieldModuleInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
      (∃ g ∈ centralizer ({t} : Set G), ∀ l ∈ L, ∃ x ∈ L, g * x * g⁻¹ ≠ l * x * l⁻¹) →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ S₀ : Subgroup G, IsLFiveFieldSylow L t (seitzTilde W₁ Kc) S₀ →
      ∃ (F : Type) (_ : Field F) (_ : Fintype F) (_ : CharP F 2) (σ : F ≃+* F),
        Nat.card F = 4 ∧ σ ≠ 1 ∧ (∀ x, σ (σ x) = x) ∧
        ∃ (ψ : seitzTilde W₁ Kc →* Matrix.SpecialLinearGroup (Fin 4) F) (β : W₁ → (Fin 4 → F)),
          Function.Surjective ψ ∧ (∀ n, ψ n = 1 ↔ (n : G) ∈ W₁) ∧
          (∀ n m : seitzTilde W₁ Kc, (m : G) = t * n * t⁻¹ →
            ((ψ m : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
              ((ψ n : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map σ) ∧
          (∀ n : seitzTilde W₁ Kc, (n : G) ∈ S₀ ↔ ψ n ∈ LinearFlag.unitriangular 4 F) ∧
          Function.Bijective β ∧ (∀ v w : W₁, β (v * w) = β v + β w) ∧
          (∀ (n : seitzTilde W₁ Kc) (w v : W₁), (v : G) = n * w * n⁻¹ →
            β v = Matrix.vecMul (β w)
              (((ψ n)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ∧
          (∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = σ ∘ β w)

@[expose] def LFiveLeviXTildeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      seitzLeviX W₁ (W₁.map (MulAut.conj d).toMonoidHom) ≤ seitzTilde W₁ Kc

@[expose] def LFiveGraphWInterInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      Nat.card (W₁ ⊓ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) ≤ 4

@[expose] def LFiveGraphLeviNormInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), SeitzSetting G L →
    ∀ (K : Type) [Field K] [CharP K 2], Nat.card K = 2 →
    ∀ (e : L ≃* LinearFlag.projectiveSL 5 K) (t : G), orderOf t = 2 →
      centralizer (L : Set G) ⊓ centralizer ({t} : Set G) = zpowers t →
    ∀ (c : Fin 5) (W₁ : Subgroup G), Nat.card W₁ = 2 ^ 8 → (∀ w ∈ W₁, w * w = 1) →
      W₁ ⊓ centralizer ({t} : Set G) = modelToG e (pointRadical c) →
    ∀ htN : t ∈ normalizer (W₁ : Set G),
      modelToG e (blockSL (K := K) ({c}ᶜ : Finset (Fin 5))) ≤ normalizer (W₁ : Set G) →
    ∀ Kc : Subgroup (seitzHat W₁), IsFieldTypeComponentAtNOne e t c W₁ htN Kc →
    ∀ (S₀ : Subgroup G) (d : G), IsLFiveGraphSylowData L t (seitzTilde W₁ Kc) S₀ d →
      CFSG.Quasithin.perfectCore (seitzTilde W₁ Kc ⊓
          normalizer ((W₁ ⊔ W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G)) ≤
        normalizer ((W₁.map (MulAut.conj d).toMonoidHom : Subgroup G) : Set G)

section Normalize

variable {G : Type*} [Group G] {F : Type} [Field F]

theorem exists_isFieldModuleData_of_conj {N W₁ S₀ S₀' : Subgroup G} {t : G} (σ : F →+* F)
    (ψ : N →* Matrix.SpecialLinearGroup (Fin 4) F) (β : W₁ → Fin 4 → F)
    (hψs : Function.Surjective ψ) (hψker : ∀ n, ψ n = 1 ↔ (n : G) ∈ W₁)
    (hψt : ∀ n m : N, (m : G) = t * n * t⁻¹ →
      ((ψ m : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F) =
        ((ψ n : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F).map σ)
    (hψS : ∀ n : N, (n : G) ∈ S₀' ↔ ψ n ∈ LinearFlag.unitriangular 4 F)
    (hβ : Function.Bijective β) (hβadd : ∀ v w : W₁, β (v * w) = β v + β w)
    (hβact : ∀ (n : N) (w v : W₁), (v : G) = n * w * n⁻¹ →
      β v = β w ᵥ* (((ψ n)⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F))
    (hβt : ∀ w v : W₁, (v : G) = t * w * t⁻¹ → β v = σ ∘ β w)
    (hW₁N : W₁ ≤ N) (hNW₁ : N ≤ normalizer (W₁ : Set G)) (hS₀N : S₀ ≤ N) {m : G} (hm : m ∈ N)
    (hS₀ : ∀ x ∈ N, x ∈ S₀ ↔ m⁻¹ * x * m ∈ S₀') :
    ∃ (p : G → Matrix.SpecialLinearGroup (Fin 4) F) (b : G → Fin 4 → F)
      (c : Matrix.SpecialLinearGroup (Fin 4) F), IsFieldModuleData N W₁ S₀ p b ∧
      (∀ x ∈ N, t * x * t⁻¹ ∈ N → (p (t * x * t⁻¹) : Matrix (Fin 4) (Fin 4) F) =
        (c : Matrix (Fin 4) (Fin 4) F) * (p x : Matrix (Fin 4) (Fin 4) F).map σ *
          ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) ∧
      (∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ → b (t * w * t⁻¹) =
        (fun k => σ (b w k)) ᵥ*
          ((c⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) : Matrix (Fin 4) (Fin 4) F)) := by
  classical
  set g := ψ ⟨m, hm⟩ with hg
  let p : G → Matrix.SpecialLinearGroup (Fin 4) F := fun x =>
    if hx : x ∈ N then g⁻¹ * ψ ⟨x, hx⟩ * g else 1
  let b : G → Fin 4 → F := fun x =>
    if hx : x ∈ W₁ then β ⟨x, hx⟩ ᵥ* (g : Matrix (Fin 4) (Fin 4) F) else 0
  have hp : ∀ x (hx : x ∈ N), p x = g⁻¹ * ψ ⟨x, hx⟩ * g := fun x hx => dite_eq_left hx
  have hb : ∀ x (hx : x ∈ W₁), b x = β ⟨x, hx⟩ ᵥ* (g : Matrix (Fin 4) (Fin 4) F) :=
    fun x hx => dite_eq_left hx
  have hgg : ∀ M : Matrix.SpecialLinearGroup (Fin 4) F,
      ((M : Matrix (Fin 4) (Fin 4) F) * ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) :
        Matrix (Fin 4) (Fin 4) F)) = 1 := fun M => by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  refine ⟨p, b, g⁻¹ * Matrix.SpecialLinearGroup.map σ g, ⟨hW₁N, hNW₁, hS₀N, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩, ?_, ?_⟩
  ·
    intro x hx y hy
    rw [hp _ (mul_mem hx hy), hp x hx, hp y hy,
      show (⟨x * y, mul_mem hx hy⟩ : N) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul]
    group
  ·
    intro M
    obtain ⟨n, hn⟩ := hψs (g * M * g⁻¹)
    refine ⟨n, n.2, ?_⟩
    rw [hp n n.2]
    change g⁻¹ * ψ n * g = M
    rw [hn]
    group
  ·
    intro x hx
    rw [hp x hx, ← hψker ⟨x, hx⟩]
    constructor
    · intro h1
      calc ψ ⟨x, hx⟩ = g * (g⁻¹ * ψ ⟨x, hx⟩ * g) * g⁻¹ := by group
        _ = 1 := by rw [h1]; group
    · intro h1
      rw [h1]
      group
  ·
    intro x hx
    rw [hS₀ x hx, hp x hx]
    have hmx : m⁻¹ * x * m ∈ N := mul_mem (mul_mem (inv_mem hm) hx) hm
    rw [show m⁻¹ * x * m = ((⟨m, hm⟩⁻¹ * ⟨x, hx⟩ * ⟨m, hm⟩ : N) : G) from rfl]
    rw [hψS, map_mul, map_mul, map_inv]
  ·
    intro v hv w hw
    rw [hb _ (mul_mem hv hw), hb v hv, hb w hw,
      show (⟨v * w, mul_mem hv hw⟩ : W₁) = ⟨v, hv⟩ * ⟨w, hw⟩ from rfl, hβadd, Matrix.add_vecMul]
  ·
    intro v hv w hw hvw
    rw [hb v hv, hb w hw] at hvw
    have h1 := congrArg (fun r => r ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F)) hvw
    simp only [Matrix.vecMul_vecMul, hgg, Matrix.vecMul_one] at h1
    exact congrArg Subtype.val (hβ.1 h1)
  ·
    intro r
    obtain ⟨w, hw⟩ := hβ.2 (r ᵥ* ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 4) F) :
      Matrix (Fin 4) (Fin 4) F))
    refine ⟨w, w.2, ?_⟩
    rw [hb w w.2]
    change β w ᵥ* _ = r
    rw [hw, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.vecMul_one]
  ·
    intro x hx w hw
    have hxw : x * w * x⁻¹ ∈ W₁ := (mem_normalizer_iff.1 (hNW₁ hx) w).1 hw
    rw [hb _ hxw, hβact ⟨x, hx⟩ ⟨w, hw⟩ ⟨x * w * x⁻¹, hxw⟩ rfl, hb w hw, hp x hx,
      Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.SpecialLinearGroup.coe_mul]
    congr 2
    simp only [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rfl
  ·
    intro x hx htx
    have h1 : ψ ⟨t * x * t⁻¹, htx⟩ = Matrix.SpecialLinearGroup.map σ (ψ ⟨x, hx⟩) :=
      Subtype.ext (hψt ⟨x, hx⟩ ⟨t * x * t⁻¹, htx⟩ rfl)
    have h2 : p (t * x * t⁻¹) = (g⁻¹ * Matrix.SpecialLinearGroup.map σ g) *
        Matrix.SpecialLinearGroup.map σ (p x) * (g⁻¹ * Matrix.SpecialLinearGroup.map σ g)⁻¹ := by
      rw [hp _ htx, hp x hx, h1, map_mul, map_mul, map_inv]
      group
    rw [h2, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    rfl
  ·
    intro w hw htw
    rw [hb _ htw, hβt ⟨w, hw⟩ ⟨t * w * t⁻¹, htw⟩ rfl, hb w hw]
    have h1 : (fun k => σ ((β ⟨w, hw⟩ ᵥ* (g : Matrix (Fin 4) (Fin 4) F)) k)) =
        (σ ∘ β ⟨w, hw⟩) ᵥ* (g : Matrix (Fin 4) (Fin 4) F).map σ := by
      funext k
      exact RingHom.map_vecMul σ _ _ k
    rw [h1, Matrix.vecMul_vecMul]
    congr 1
    have h2 : (g : Matrix (Fin 4) (Fin 4) F).map σ =
        ((Matrix.SpecialLinearGroup.map σ g : Matrix.SpecialLinearGroup (Fin 4) F) :
          Matrix (Fin 4) (Fin 4) F) := rfl
    rw [h2, ← Matrix.SpecialLinearGroup.coe_mul]
    congr 1
    simp only [_root_.mul_inv_rev, inv_inv, mul_inv_cancel_left]
    rfl

end Normalize

section Reduction

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_of_not_two_dvd_relIndex {N S₀ S₀' : Subgroup G} (hS₀p : IsPGroup 2 S₀)
    (hS₀odd : ¬ 2 ∣ S₀.relIndex N) (hS₀'p : IsPGroup 2 S₀') (hS₀'odd : ¬ 2 ∣ S₀'.relIndex N) :
    ∃ m ∈ N, ∀ x ∈ N, x ∈ S₀ ↔ m⁻¹ * x * m ∈ S₀' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (S₀.comap N.subtype).index := hS₀odd
  have hodd' : ¬ 2 ∣ (S₀'.comap N.subtype).index := hS₀'odd
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq N ((hS₀'p.comap_subtype (K := N)).toSylow hodd')
    ((hS₀p.comap_subtype (K := N)).toSylow hodd)
  refine ⟨m, m.2, fun x hx => ?_⟩
  have h1 : (⟨x, hx⟩ : N) ∈ (((hS₀p.comap_subtype (K := N)).toSylow hodd : Sylow 2 N) :
        Subgroup N) ↔
      (⟨x, hx⟩ : N) ∈ ((m • (hS₀'p.comap_subtype (K := N)).toSylow hodd' : Sylow 2 N) :
        Subgroup N) := by rw [hm]
  rw [IsPGroup.toSylow_coe, Sylow.coe_subgroup_smul,
    Subgroup.mem_pointwise_smul_iff_inv_smul_mem, IsPGroup.toSylow_coe] at h1
  have h2 : x ∈ S₀ ↔ (⟨x, hx⟩ : N) ∈ S₀.comap N.subtype := Iff.rfl
  rw [← map_inv, MulAut.smul_def, MulAut.conj_apply, inv_inv] at h1
  rw [h2, h1, mem_comap]
  exact Iff.rfl

theorem lFiveGraphLeviInput_of_fieldModule
    (h : LFiveWOneFieldModuleInput)
    (h₁ : LFiveLeviXTildeInput) (h₂ : LFiveGraphWInterInput) (h₃ : LFiveGraphLeviNormInput) :
    LFiveGraphLeviInput := by
  intro G _ _ L hset K _ _ hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  have hZ := h₂ G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  have hXN := h₁ G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  have hP3 := h₃ G L hset K hK e t ht hKt c W₁ hW₁c hW₁2 hW₁t htN hLN Kc hKc S₀ d hdata
  obtain ⟨-, -, -, -, htW₂, -⟩ := graph_swap_facts_of_sylowData htN hdata
  obtain ⟨hS₀p, hS₀N, hS₀odd, -, hdS₀, hdt, -, hdo⟩ := hdata
  set N := seitzTilde W₁ Kc with hNdef
  set W₂ := W₁.map (MulAut.conj d).toMonoidHom with hW₂def
  have hW₁N : W₁ ≤ N := fun w hw => mem_seitzTilde_iff.2 ⟨le_normalizer hw, by
    rw [show QuotientGroup.mk' (W₁.subgroupOf (normalizer (W₁ : Set G))) ⟨w, le_normalizer hw⟩ = 1
      from (QuotientGroup.eq_one_iff _).2 (mem_subgroupOf.2 hw)]
    exact one_mem _⟩
  have hNW₁ : N ≤ normalizer (W₁ : Set G) := seitzTilde_le_normalizer W₁ Kc
  have hW₁S₀ : W₁ ≤ S₀ :=
    wOne_le_of_not_two_dvd_relIndex (IsPGroup.of_card hW₁c) hNW₁ hS₀p hS₀N hW₁N hS₀odd
  obtain ⟨S₀', hS₀'⟩ := exists_lFiveFieldSylow hset hK e ht hKt c hW₁c hW₁2 hW₁t htN hLN hKc
  obtain ⟨F, _, _, _, σ, hF, hσ1, -, ψ, β, hψs, hψker, hψt, hψS, hβ, hβadd, hβact, hβt⟩ :=
    h G L hset K hK e t ht hKt ⟨d, mem_centralizer_singleton_iff.2 hdt, hdo⟩ c W₁ hW₁c hW₁2 hW₁t
      htN hLN Kc hKc S₀' hS₀'
  have hσ : ∀ x, (σ : F →+* F) x = x ^ 2 := by
    rcases ringEquiv_eq_id_or_sq_of_card_four hF σ with h1 | h1
    · exact absurd (RingEquiv.ext fun x => (h1 x).trans rfl) hσ1
    · exact h1
  obtain ⟨m, hm, hS₀m⟩ :=
    exists_conj_of_not_two_dvd_relIndex hS₀p hS₀odd hS₀'.1 hS₀'.2.2.1
  obtain ⟨p, b, c', hdat, hpt, hbt⟩ := exists_isFieldModuleData_of_conj (σ : F →+* F) ψ β hψs
    hψker hψt hψS hβ hβadd hβact hβt hW₁N hNW₁ hS₀N hm hS₀m
  have hW₂S₀ : W₂ ≤ S₀ := by
    rintro _ ⟨w, hw, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact (mem_normalizer_iff.1 hdS₀ w).1 (hW₁S₀ hw)
  have hS₀W₂ : S₀ ≤ normalizer (W₂ : Set G) := by
    refine le_normalizer_of_forall_conj_mem fun s hs x hx => ?_
    obtain ⟨w, hw, rfl⟩ := hx
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hs' : d⁻¹ * s * d ∈ S₀ := by
      have h1 := (mem_normalizer_iff.1 (inv_mem hdS₀) s).1 hs
      rwa [inv_inv] at h1
    have hw' := (mem_normalizer_iff.1 (hNW₁ (hS₀N hs')) w).1 hw
    refine ⟨d⁻¹ * s * d * w * (d⁻¹ * s * d)⁻¹, hw', ?_⟩
    rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have hW₂c : Nat.card W₂ = 2 ^ 8 := by
    rw [hW₂def, Subgroup.card_map_of_injective (MulAut.conj d).injective, hW₁c]
  have htW₁ : ∀ w ∈ W₁, t * w * t⁻¹ ∈ W₁ := fun w hw => (mem_normalizer_iff.1 htN w).1 hw
  obtain ⟨φ, hφs, hφker, hS₀X, hB, hμ₁, hμ₂⟩ := exists_leviData_of_fieldModule hF hdat hW₂S₀
    hS₀W₂ hW₂c hZ hXN hP3 hσ hpt (fun w hw => hbt w hw (htW₁ w hw)) htW₁ htW₂
  exact ⟨F, inferInstance, inferInstance, hF, φ, hφs, hφker, hS₀X, hB, hμ₁, hμ₂⟩

end Reduction

end CFSG.SeitzReduction.LinearPilot
