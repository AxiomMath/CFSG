module

public import CFSG.CGT.PushingUpLit.A78.BenderTIBasic
public import CFSG.CGT.PushingUpLit.A78G0.TorusK

public section

namespace CFSG.CGT.PushingUpLit.A78G0

open CFSG.Timmesfeld.ARS CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
  CFSG.CGT.PushingUpLit.A78S4 CFSG.CGT.PushingUpLit.A78L3 CFSG.ABGLocalTools Matrix

section Generic

variable {X : Type} [Group X] [Finite X]

theorem isSylowOf_of_mem_normalizer {R C : Subgroup X} (hRC : R ≤ C) (hR : IsPGroup 2 R)
    (h : ∀ x ∈ C, x ∈ Subgroup.normalizer (R : Set X) → (∃ k : ℕ, x ^ 2 ^ k = 1) → x ∈ R) :
    IsSylowOf 2 R C := by
  have hR' : IsPGroup 2 (R.subgroupOf C) := hR.comap_subtype
  obtain ⟨S, hS⟩ := exists_sylow_eq_of_forall_mem_normalizer hR' (fun x hx hx2 => by
    have hxN : (x : X) ∈ Subgroup.normalizer (R : Set X) := by
      rw [Subgroup.mem_normalizer_iff] at hx ⊢
      intro r
      constructor
      · intro hr
        have := (hx ⟨r, hRC hr⟩).1 (Subgroup.mem_subgroupOf.2 hr)
        exact Subgroup.mem_subgroupOf.1 this
      · intro hr
        have hrC : r ∈ C := by
          have h1 : (x : X)⁻¹ * ((x : X) * r * (x : X)⁻¹) * x ∈ C :=
            C.mul_mem (C.mul_mem (C.inv_mem x.2) (hRC hr)) x.2
          simpa [mul_assoc] using h1
        have := (hx ⟨r, hrC⟩).2 (Subgroup.mem_subgroupOf.2 hr)
        exact Subgroup.mem_subgroupOf.1 this
    exact Subgroup.mem_subgroupOf.2 (h x x.2 hxN (by
      obtain ⟨k, hk⟩ := hx2
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩)))
  exact ⟨S, by rw [hS, Subgroup.map_subgroupOf_eq_of_le hRC]⟩

end Generic

section Img

variable {G : Type} [Group G] {L V : Subgroup G} {e : ℕ}
  (φ : ↥L →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e))

theorem card_img_of_inf (hk : φ.ker = V.subgroupOf L) {B : Subgroup G} (hBL : B ≤ L)
    (hBV : B ⊓ V = ⊥) : Nat.card (img φ B) = Nat.card B := by
  let f : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e) :=
    φ.comp (Subgroup.inclusion hBL)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have h1 : (Subgroup.inclusion hBL b : ↥L) ∈ φ.ker := by
      rw [MonoidHom.mem_ker]
      exact hb
    rw [hk, Subgroup.mem_subgroupOf] at h1
    have h2 : (b : G) ∈ B ⊓ V := ⟨b.2, h1⟩
    rw [hBV, Subgroup.mem_bot] at h2
    exact Subtype.ext h2
  have hrange : f.range = img φ B := by
    ext y
    rw [MonoidHom.mem_range, mem_img]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨Subgroup.inclusion hBL x, x.2, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, hc⟩, rfl⟩
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm

end Img

namespace G0Core

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ : Subgroup G} {e : ℕ}
  (h : G0Core G L₁ L₂ V W Z Z₂ e)

include h

theorem mem_L_of_two_elt {x : G} (hx : x ∈ Subgroup.normalizer (V : Set G))
    (h2 : ∃ k : ℕ, x ^ 2 ^ k = 1) : x ∈ L₁ := by
  obtain ⟨n, hn⟩ := h2
  have hE2 : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    rintro ⟨s, hs⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hn,
      _root_.one_zpow]
  have hEM : Subgroup.zpowers x ≤ Subgroup.normalizer (V : Set G) := by
    rw [Subgroup.zpowers_le]
    exact hx
  obtain ⟨k, hk, hkE⟩ := exists_conj_le_of_isSylowOf h.side₁.sylow_T hEM hE2
  have hxk : k * x * k⁻¹ ∈ V ⊔ W := hkE (conj_mem_cs k (Subgroup.mem_zpowers x))
  have h1 : k * x * k⁻¹ ∈ L₁ := h.J_le_L hxk
  have h2 := conj_mem_of_mem_normalizer' (Subgroup.inv_mem _ (h.M_le_normalizer_L hk)) h1
  simpa [mul_assoc] using h2

theorem exists_mem_cliq_rho (D : NatCoordK G L₁ V Z (GaloisField 2 e))
    (fr : S4Side.Frame h.pair.side₁ D) {B : Subgroup G} (hB : B ∈ cliq Z W)
    {u : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 e)}
    (hu : (u : Matrix (Fin 2) (Fin 2) (GaloisField 2 e)) *ᵥ D.κ fr.n₀ = D.κ fr.n₀) :
    ∃ p ∈ B, D.ρ p = u := by
  set φ := rhoHom D with hφ
  have hk := rhoHom_ker D
  have hJq : Nat.card (img φ (V ⊔ W)) = 2 ^ e :=
    card_img_eq φ hk le_sup_left h.J_le_L h.card_J
  have hBL : B ≤ L₁ := hB.2.2.trans (le_sup_right.trans h.J_le_L)
  have hBcard : Nat.card B = 2 ^ e := by
    obtain ⟨g, hg⟩ := hB.1
    have hg' : B = cs Z g := hg.symm
    rw [hg', card_cs, h.card_Z]
  have hcB : Nat.card (img φ B) = 2 ^ e :=
    (card_img_of_inf φ hk hBL (h.inf_V_of_mem_cliq hB)).trans hBcard
  have hle : img φ B ≤ img φ (V ⊔ W) := img_le_of_le φ (hB.2.2.trans le_sup_right)
  have heq : img φ B = img φ (V ⊔ W) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcB, hJq])
  obtain ⟨l, hl, rfl⟩ := D.ρ_surj u
  have hlJ : l ∈ V ⊔ W := (h.pair.side₁.mem_J_iff D fr.hn₀ fr.hn₀Z hl).2 hu
  have hmem : D.ρ l ∈ img φ B := by
    rw [heq]
    exact (mem_img φ).2 ⟨⟨l, hl⟩, hlJ, rfl⟩
  obtain ⟨c, hcB', hc⟩ := (mem_img φ).1 hmem
  exact ⟨c, hcB', (rhoHom_apply D c).symm.trans hc⟩

theorem torus₀_of_scalar (D : NatCoordK G L₁ V Z (GaloisField 2 e)) {x : G}
    (hxN : x ∈ Subgroup.normalizer (V : Set G)) {lam : GaloisField 2 e} (hlam : lam ≠ 0)
    (hact : ∀ w, D.act x w = lam • w) (hcentZ : ∀ z ∈ Z, x * z * x⁻¹ = z → z = 1) :
    Torus₀ h x ∧ lam ≠ 1 := by
  have hxNZ : x ∈ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (Z : Set G) :=
    ⟨hxN, by rw [h.normalizer_Z_eq]; exact hxN⟩
  have hxNL : x ∈ Subgroup.normalizer (L₁ : Set G) := h.M_le_normalizer_L hxN
  have hcommL : ∀ l ∈ L₁, x * l * x⁻¹ * l⁻¹ ∈ V := fun l hl =>
    comm_mem_V_of_scalar D hxNL hxNZ hlam hact hl
  have hlam1 : lam ≠ 1 := by
    intro hl1
    have hV' : ∀ v ∈ V, x * v * x⁻¹ * v⁻¹ ∈ Z := fun v hv =>
      comm_mem_K_of_one D hxNZ (fun w => by rw [hact w, hl1]) hv
    have hcent := h.cent_comm_of_trivial hcommL hV'
    obtain ⟨z, hz, hz1⟩ := h.ex_ne_one_Z
    have hzc := hcent (h.V_le_comm (h.Z_le_V hz))
    rw [Subgroup.mem_centralizer_singleton_iff] at hzc
    apply hz1
    apply hcentZ z hz
    rw [← hzc]
    group
  exact ⟨⟨hxN, hcommL, fun v hv hyv =>
    hcentZ v (mem_K_of_centralizes D hxNZ hlam1 hact hv hyv) hyv⟩, hlam1⟩

end G0Core

end CFSG.CGT.PushingUpLit.A78G0
