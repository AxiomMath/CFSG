module

public import CFSG.Goldschmidt.Steps.G73Basic
import CFSG.Walter.Bender1970.S4.Types
import CFSG.Walter.Bender1970.S4.ComponentTools

public section

namespace CFSG.Goldschmidt

namespace G73

section Adm

variable {G : Type} [Group G]

@[expose] def Adm (A K J : Subgroup G) : Prop :=
  (∃ g : G, ¬ conjSub g A ⊓ J ≤ Subgroup.centralizer (J : Set G)) ∧ (IsGoldL2 J → IsGoldL2 K)

theorem adm_map_conj {A K J : Subgroup G} (c : G) (h : Adm A K J) :
    Adm A K (J.map (MulAut.conj c).toMonoidHom) := by
  obtain ⟨⟨g, hg⟩, hL2⟩ := h
  refine ⟨⟨g * c⁻¹, fun hle => hg fun x hx => ?_⟩, fun hJ => hL2 ?_⟩
  · have hx1 : g * x * g⁻¹ ∈ A := mem_conjSub.mp hx.1
    have h1 : c * x * c⁻¹ ∈ conjSub (g * c⁻¹) A ⊓ J.map (MulAut.conj c).toMonoidHom :=
      ⟨mem_conjSub.mpr (by simpa [mul_assoc] using hx1), ⟨x, hx.2, by simp [MulAut.conj_apply]⟩⟩
    have h2 := hle h1
    rw [Subgroup.mem_centralizer_iff] at h2 ⊢
    intro y hy
    have h3 := h2 (c * y * c⁻¹) ⟨y, hy, by simp [MulAut.conj_apply]⟩
    have h4 : c * (y * x) * c⁻¹ = c * (x * y) * c⁻¹ := by
      calc c * (y * x) * c⁻¹ = c * y * c⁻¹ * (c * x * c⁻¹) := by group
        _ = c * x * c⁻¹ * (c * y * c⁻¹) := h3
        _ = c * (x * y) * c⁻¹ := by group
    simpa using h4
  · exact (CFSG.Walter.isTypeL2Odd_map_conj_iff J c).mp hJ

theorem adm_self {A K : Subgroup G} (hK : ¬ A ⊓ K ≤ Subgroup.centralizer (K : Set G)) :
    Adm A K K :=
  ⟨⟨1, by rwa [conjSub_one]⟩, id⟩

end Adm

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {A : Subgroup G}

theorem isComponentOf_of_le (h37 : S_G37) (hG : GoldSetting G S A) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) {H : Subgroup G} (hH : H ∈ CFSG.Walter.benderM a) {a₁ : G} (ha₁ : a₁ ∈ A)
    {H₁ : Subgroup G} (hH₁ : H₁ ∈ CFSG.Walter.benderM a₁) {J : Subgroup G}
    (hJ : GorensteinWalter.IsComponentOf J H) (hJH₁ : J ≤ H₁)
    (hJO : J ≤ Subgroup.centralizer (oddCoreOf H₁ : Set G))
    (hres : IsGoldL2 J → ∀ L : Subgroup G,
      GorensteinWalter.IsComponentOf L (normalClosureIn H₁ A) → IsGoldL2 L) :
    GorensteinWalter.IsComponentOf J H₁ := by
  have hS₁ := isSStarIn_of_mem_benderM hG ha₁ hH₁
  set X := GorensteinWalter.componentLayerOf (H₁ ⊓ GorensteinWalter.componentLayerOf H) with hX
  have hXH₁ : X ≤ H₁ := (GorensteinWalter.componentLayerOf_isNormalIn _).1.trans inf_le_left
  have hXn : H₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤ Subgroup.normalizer (X : Set G) := by
    intro h hh
    have hhH : h ∈ H := CFSG.Walter.centralizer_le_of_mem_benderM hH hh.2
    exact CFSG.Walter.mem_normalizer_componentLayerOf
      (Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hh.1,
        CFSG.Walter.mem_normalizer_componentLayerOf (Subgroup.le_normalizer hhH)⟩)
  have hJX : GorensteinWalter.IsComponentOf J X := by
    have hJE : J ≤ GorensteinWalter.componentLayerOf H :=
      CFSG.Walter.le_componentLayerOf_of_isComponentOf hJ
    have h1 : GorensteinWalter.IsComponentOf J (H₁ ⊓ GorensteinWalter.componentLayerOf H) :=
      CFSG.Walter.isComponentOf_of_le hJ (le_inf hJH₁ hJE)
        (inf_le_right.trans (GorensteinWalter.componentLayerOf_isNormalIn H).1)
    exact CFSG.Walter.isComponentOf_of_le h1 (CFSG.Walter.le_componentLayerOf_of_isComponentOf h1)
      (GorensteinWalter.componentLayerOf_isNormalIn _).1
  obtain ⟨-, h2, -⟩ := h37 G H₁ A hS₁ hG.elem a ha ha1 X hXH₁ hXn (componentLayerOf_eq_sup _)
  obtain ⟨L, hL, -, hcase⟩ := h2 J hJX hJO
  rcases hcase with h | ⟨hJ2, -, hLJR, hLQ⟩
  · exact h ▸ hL
  · exact absurd (hres hJ2 L (CFSG.Walter.isComponentOf_of_le hL hLQ (normalClosureIn_le H₁ A)))
      (CFSG.Walter.not_isTypeL2Odd_of_isTypeJR hLJR)

theorem centralizer_le (h31 : S_G31) (h37 : S_G37) (h71 : S_G71) (hG : GoldSetting G S A)
    (h8 : 8 ≤ Nat.card A) {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) {H : Subgroup G}
    (hH : H ∈ CFSG.Walter.benderM a) {K : Subgroup G}
    (hK : GorensteinWalter.IsComponentOf K (normalClosureIn H A))
    (hch : IsGoldL2 K → ∀ a' ∈ A, a' ≠ 1 → ∀ H' ∈ CFSG.Walter.benderM a', ∀ K' : Subgroup G,
      GorensteinWalter.IsComponentOf K' (normalClosureIn H' A) → IsGoldL2 K') :
    Subgroup.centralizer (K : Set G) ≤ H ∧
      Subgroup.normalizer ((sSup {J | GorensteinWalter.IsComponentOf J H ∧ Adm A K J} :
        Subgroup G) : Set G) = H ∧
      sSup {J | GorensteinWalter.IsComponentOf J H ∧ Adm A K J} =
        K ⊔ sSup {J | GorensteinWalter.IsComponentOf J (Subgroup.centralizer (K : Set G)) ∧
          Adm A K J} := by
  have := hG.isSimpleGroup
  have hS := isSStarIn_of_mem_benderM hG ha hH
  have hAH := le_of_mem_benderM hG ha hH
  have hKH := isComponentOf_of_normalClosureIn hK
  have hKA := not_inf_le_centralizer h31 hS hG.elem hK
  obtain ⟨a₁, ha₁, ha₁1⟩ : ∃ a₁ ∈ A ⊓ K, a₁ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hKA fun x hx => by rw [hcon x hx]; exact Subgroup.one_mem _
  obtain ⟨H₁, hH₁⟩ := benderM_nonempty hG ha₁1
  have hCH₁ : Subgroup.centralizer (K : Set G) ≤ H₁ :=
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr ha₁.2)).trans
      (CFSG.Walter.centralizer_le_of_mem_benderM hH₁)
  refine CFSG.Walter.centralizer_le_and_eq_of_forall_isComponentOf
    (CFSG.Walter.isCoatom_of_mem_benderM hH) hKH (Adm A K) (fun J c hJ => adm_map_conj c hJ)
    (adm_self hKA) fun J hJ hJadm hJK => ?_
  have hJC : J ≤ Subgroup.centralizer (K : Set G) :=
    CFSG.Walter.le_centralizer_of_isComponentOf_ne hJ hKH hJK
  have hJH₁ : J ≤ H₁ := hJC.trans hCH₁
  obtain ⟨⟨g, hg⟩, hJL2⟩ := hJadm
  have hJQ : GorensteinWalter.IsComponentOf J (normalClosureIn H A) :=
    CFSG.Walter.isComponentOf_of_le hJ (le_normalClosureIn_of_not_le hG hAH hJ hg)
      (normalClosureIn_le H A)
  have hJQ₁ : J ≤ normalClosureIn H₁ A :=
    (le_normalClosureIn_self h31 hS hG.elem hJQ).trans (normalClosureIn_mono hJH₁)
  have hJO₁ := (le_centralizer_oddCoreOf_of_le h71 hG h8 ha₁.1 ha₁1 hH₁
    (commutator_self_of_isComponentOf hJ) hJQ₁).2
  have hJH₁' := isComponentOf_of_le h37 hG ha ha1 hH ha₁.1 hH₁ hJ hJH₁ hJO₁
    fun hJ2 L hL => hch (hJL2 hJ2) a₁ ha₁.1 ha₁1 H₁ hH₁ L hL
  exact CFSG.Walter.isComponentOf_of_le hJH₁' hJC hCH₁

end G73

open G73 in
theorem G73_of (h31 : S_G31) (h37 : S_G37) (h71 : S_G71) : S_G73 := by
  intro G _ _ S A hG h8 a ha ha1 H hH K hK hch a₀ ha₀ ha₀1
  obtain ⟨-, hNH, hNeq⟩ := centralizer_le h31 h37 h71 hG h8 ha ha1 hH hK hch
  have hS := isSStarIn_of_mem_benderM hG ha hH
  have hKH := isComponentOf_of_normalClosureIn hK
  have hKC : K ≤ Subgroup.centralizer ({a₀} : Set G) := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mpr ((Subgroup.mem_centralizer_iff.mp ha₀.2) k hk)
  have key : ∀ H₀ ∈ CFSG.Walter.benderM a₀, H₀ = H := by
    intro H₀ hH₀
    have hKH₀ : K ≤ H₀ := hKC.trans (CFSG.Walter.centralizer_le_of_mem_benderM hH₀)
    have hKQ₀ : K ≤ normalClosureIn H₀ A :=
      (le_normalClosureIn_self h31 hS hG.elem hK).trans (normalClosureIn_mono hKH₀)
    have hKO₀ := (le_centralizer_oddCoreOf_of_le h71 hG h8 ha₀.1 ha₀1 hH₀
      (commutator_self_of_isComponentOf hK) hKQ₀).2
    have hKH₀' := isComponentOf_of_le h37 hG ha ha1 hH ha₀.1 hH₀ hKH hKH₀ hKO₀
      fun hK2 L hL => hch hK2 a₀ ha₀.1 ha₀1 H₀ hH₀ L hL
    have hK₀ : GorensteinWalter.IsComponentOf K (normalClosureIn H₀ A) :=
      CFSG.Walter.isComponentOf_of_le hKH₀' hKQ₀ (normalClosureIn_le H₀ A)
    obtain ⟨-, hNH₀, hNeq₀⟩ := centralizer_le h31 h37 h71 hG h8 ha₀.1 ha₀1 hH₀ hK₀ hch
    rw [← hNH₀, hNeq₀, ← hNeq, hNH]
  obtain ⟨H₀, hH₀⟩ := benderM_nonempty hG ha₀1
  rw [Set.eq_singleton_iff_unique_mem]
  exact ⟨key H₀ hH₀ ▸ hH₀, key⟩

end CFSG.Goldschmidt
