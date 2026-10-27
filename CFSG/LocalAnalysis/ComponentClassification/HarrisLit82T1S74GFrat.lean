module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74GZstar
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Bypass

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74

open CFSG Subgroup CFSG.LieType.Universal.Spin

theorem map_oddCore {X G : Type*} [Group X] [Group G] (φ : X →* G) (hφ : Function.Injective φ)
    (A : Subgroup X) :
    ((pPrimeCore 2 ↥A).map A.subtype).map φ = (pPrimeCore 2 ↥(A.map φ)).map (A.map φ).subtype := by
  let e : ↥A ≃* ↥(A.map φ) := A.equivMapOfInjective φ hφ
  rw [← pPrimeCore_map_iso 2 e, map_map, map_map]
  rfl

theorem eq_or_eq_of_relIndex_eq_two {G : Type*} [Group G] {B A S₀ : Subgroup G} (hBA : B ≤ A)
    (hAS : A ≤ S₀) (h2 : B.relIndex S₀ = 2) : A = B ∨ A = S₀ := by
  have h := Subgroup.relIndex_mul_relIndex _ _ _ hBA hAS
  rw [h2] at h
  rcases Nat.prime_two.eq_one_or_self_of_dvd (B.relIndex A) ⟨_, h.symm⟩ with h1 | h1
  · left
    exact le_antisymm (relIndex_eq_one.mp h1) hBA
  · right
    rw [h1] at h
    have : A.relIndex S₀ = 1 := by omega
    exact le_antisymm hAS (relIndex_eq_one.mp this)

namespace Setup

variable {G : Type} [Group G] [Finite G] (S : Setup G)

theorem T_eq : S.T = closure {S.z, S.t} := by
  change (closure ({spinZ S.K, tSeven S.K} : Set S.X)).map S.φ = _
  rw [MonoidHom.map_closure, Set.image_pair, S.hφz]

theorem mem_T {x : G} (hx : x ∈ S.T) : x = 1 ∨ x = S.z ∨ x = S.t ∨ x = S.z * S.t := by
  obtain ⟨hzz, -, htt, -, hzt, -⟩ := S.facts
  have hle : S.T ≤ CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions S.z S.t hzz htt hzt := by
    rw [S.T_eq, closure_le]
    rintro _ (rfl | rfl)
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
  rcases hle hx with h | h | h | h
  · exact Or.inr (Or.inr (Or.inr h))
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inl h

theorem z_mem_T : S.z ∈ S.T := by
  rw [S.T_eq]
  exact subset_closure (Set.mem_insert _ _)

theorem t_mem_T : S.t ∈ S.T := by
  rw [S.T_eq]
  exact subset_closure (Set.mem_insert_of_mem _ rfl)

theorem mem_normalizer_T {g : G} (hz : g * S.z * g⁻¹ ∈ S.T) (ht : g * S.t * g⁻¹ ∈ S.T) :
    g ∈ normalizer (S.T : Set G) := by
  have hle : S.T.map (MulAut.conj g).toMonoidHom ≤ S.T := by
    rw [S.T_eq, MonoidHom.map_closure, closure_le, Set.image_pair]
    rintro _ (rfl | rfl)
    · rw [← S.T_eq]
      exact hz
    · rw [← S.T_eq]
      exact ht
  have heq : S.T.map (MulAut.conj g).toMonoidHom = S.T :=
    eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← heq]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by simpa using hyx
    rw [← this]
    exact hy

theorem mem_normalizer_T_of_commute {g : G} (hz : g * S.z = S.z * g) (ht : g * S.t = S.t * g) :
    g ∈ normalizer (S.T : Set G) := by
  refine S.mem_normalizer_T ?_ ?_
  · rw [hz, mul_inv_cancel_right]
    exact S.z_mem_T
  · rw [ht, mul_inv_cancel_right]
    exact S.t_mem_T

theorem conj_t_of_mem_normalizer {m : G} (hmH : m ∈ S.H) (hmN : m ∈ normalizer (S.T : Set G)) :
    m * S.t * m⁻¹ = S.t ∨ m * S.t * m⁻¹ = S.z * S.t := by
  obtain ⟨-, -, -, ht1, -, hzt', -⟩ := S.facts
  have hmz : m * S.z = S.z * m := mem_centralizer_singleton_iff.mp hmH
  rcases S.mem_T ((mem_normalizer_iff.mp hmN S.t).mp S.t_mem_T) with h | h | h | h
  · exfalso
    apply ht1
    calc S.t = m⁻¹ * (m * S.t * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  · exfalso
    apply hzt'
    calc S.z = m⁻¹ * (m * S.z) := by group
      _ = m⁻¹ * (S.z * m) := by rw [hmz]
      _ = m⁻¹ * (m * S.t * m⁻¹) * m := by rw [h]; group
      _ = S.t := by group
  · exact Or.inl h
  · exact Or.inr h

theorem map_inf_centralizer (A : Subgroup S.X) (x : S.X) :
    (A ⊓ centralizer ({x} : Set S.X)).map S.φ = A.map S.φ ⊓ centralizer ({S.φ x} : Set G) := by
  rw [S.map_inf, S.map_centralizer, ← inf_assoc, inf_of_le_left (S.map_le_L A)]

theorem map_normalizer_le : (normalizer (fourT S.K : Set S.X)).map S.φ ≤
    normalizer (S.T : Set G) := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_normalizer_iff] at hx
  rw [mem_normalizer_iff]
  intro g
  constructor
  · intro hg
    obtain ⟨y, hy, rfl⟩ := hg
    exact ⟨x * y * x⁻¹, (hx y).mp hy, by simp⟩
  · intro hg
    obtain ⟨w, hw, hwg⟩ := hg
    refine ⟨x⁻¹ * w * x, (hx _).mpr (by simpa [mul_assoc] using hw), ?_⟩
    rw [map_mul, map_mul, map_inv, hwg]
    group

theorem le_map_normalizer : S.L ⊓ normalizer (S.T : Set G) ≤
    (normalizer (fourT S.K : Set S.X)).map S.φ := by
  intro g hg
  obtain ⟨hgL, hgN⟩ := mem_inf.mp hg
  obtain ⟨x, rfl⟩ := S.exists_eq_of_mem_L hgL
  refine ⟨x, ?_, rfl⟩
  rw [SetLike.mem_coe]
  rw [mem_normalizer_iff] at hgN ⊢
  intro y
  have h := hgN (S.φ y)
  have e1 : S.φ y ∈ S.T ↔ y ∈ fourT S.K :=
    ⟨fun ⟨w, hw, hwy⟩ => S.hφ hwy ▸ hw, fun hy => ⟨y, hy, rfl⟩⟩
  have e2 : S.φ x * S.φ y * (S.φ x)⁻¹ ∈ S.T ↔ x * y * x⁻¹ ∈ fourT S.K := by
    rw [← map_inv, ← map_mul, ← map_mul]
    exact ⟨fun ⟨w, hw, hwy⟩ => S.hφ hwy ▸ hw, fun hy => ⟨_, hy, rfl⟩⟩
  rw [e1, e2] at h
  exact h

variable {iX : S.X} {S₀ B : Subgroup S.X}

abbrev M : Subgroup G := S.Y ⊓ normalizer (S.T : Set G) ⊓ S.H

abbrev K₃ : Subgroup G := (pPrimeCore 2 ↥(S.L ⊓ S.Y)).map (S.L ⊓ S.Y).subtype

theorem L_inf_Y : S.L ⊓ S.Y = (centralizer ({qThree S.K} : Set S.X)).map S.φ :=
  (S.map_centralizer _).symm

theorem inf_centralizer_t (hSy : SylowFacts S.K iX S₀ B) (hI : IBarFacts S.K S.p iX) :
    S₀ ⊓ centralizer ({tSeven S.K} : Set S.X) = B := by
  have hBle : B ≤ S₀ ⊓ centralizer ({tSeven S.K} : Set S.X) := fun x hx =>
    ⟨hSy.B_le hx, mem_centralizer_singleton_iff.mpr (hSy.commute_t x hx).symm⟩
  rcases eq_or_eq_of_relIndex_eq_two hBle inf_le_left hSy.relIndex_B with h | h
  · exact h
  · exfalso
    have hi : iX ∈ S₀ ⊓ centralizer ({tSeven S.K} : Set S.X) := by
      rw [h]
      exact hSy.i_mem
    have hi' := mem_centralizer_singleton_iff.mp (mem_inf.mp hi).2
    have h1 : iX * tSeven S.K * iX⁻¹ = tSeven S.K := by rw [hi']; group
    have hct := hI.conj_t
    rw [h1] at hct
    obtain ⟨-, hz1, -⟩ := spinZ_facts S.hp S.hp2 S.hK
    apply hz1
    calc spinZ S.K = spinZ S.K * tSeven S.K * (tSeven S.K)⁻¹ := by group
      _ = 1 := by rw [← hct]; group

theorem mem_normalizer_T_of_normalizer_S₀ (hSy : SylowFacts S.K iX S₀ B)
    (hI : IBarFacts S.K S.p iX) {m : G} (hmH : m ∈ S.H)
    (hmN : m ∈ normalizer (S.S₀G S₀ : Set G)) : m ∈ normalizer (S.T : Set G) := by
  obtain ⟨hzz, hz1, htt, ht1, hzt, hzt', -⟩ := S.facts
  have hmz : m * S.z = S.z * m := mem_centralizer_singleton_iff.mp hmH
  refine S.mem_normalizer_T (by rw [hmz, mul_inv_cancel_right]; exact S.z_mem_T) ?_
  have htS : S.t ∈ S.S₀G S₀ := ⟨tSeven S.K, hSy.B_le hSy.t_mem, rfl⟩
  obtain ⟨u, hu, hut⟩ := (mem_normalizer_iff.mp hmN S.t).mp htS
  have hcard : Nat.card ↥(S₀ ⊓ centralizer ({u} : Set S.X)) = Nat.card B := by
    rw [← S.card_map, S.map_inf_centralizer, hut, ← inf_centralizer_t S hSy hI, ← S.card_map,
      S.map_inf_centralizer]
    exact card_inf_centralizer_conj hmN S.t
  have huu : u * u = 1 := S.hφ (by
    rw [map_mul, hut, map_one]
    calc m * S.t * m⁻¹ * (m * S.t * m⁻¹) = m * (S.t * S.t) * m⁻¹ := by group
      _ = 1 := by rw [htt]; group)
  by_cases huB : u ∈ B
  · rcases hSy.involutions_B u huB huu with rfl | rfl | rfl | rfl
    · exfalso
      apply ht1
      rw [map_one] at hut
      calc S.t = m⁻¹ * (m * S.t * m⁻¹) * m := by group
        _ = 1 := by rw [← hut]; group
    · exfalso
      apply hzt'
      rw [S.hφz] at hut
      calc S.z = m⁻¹ * (m * S.z) := by group
        _ = m⁻¹ * (S.z * m) := by rw [hmz]
        _ = m⁻¹ * (m * S.t * m⁻¹) * m := by rw [← hut]; group
        _ = S.t := by group
    · rw [← hut]
      exact S.t_mem_T
    · rw [← hut, map_mul, S.hφz]
      exact mul_mem S.z_mem_T S.t_mem_T
  · exfalso
    obtain ⟨s, hs, hsi⟩ := hSy.conj_i u hu huB huu
    apply hSy.card_i
    rw [← hcard, ← hsi]
    exact (card_inf_centralizer_conj (le_normalizer hs) iX).symm

omit [Finite G] in
theorem mem_normalizer_of_map_eq {A : Subgroup G} {g : G}
    (h : A.map (MulAut.conj g).toMonoidHom = A) : g ∈ normalizer (A : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := by simpa using hyx
    rw [← this]
    exact hy

theorem map_conj_LY {g : G} (hg : g ∈ S.Y ⊓ S.H) :
    (S.L ⊓ S.Y).map (MulAut.conj g).toMonoidHom = S.L ⊓ S.Y := by
  obtain ⟨hgY, hgH⟩ := mem_inf.mp hg
  have hle : (S.L ⊓ S.Y).map (MulAut.conj g).toMonoidHom ≤ S.L ⊓ S.Y := by
    rintro _ ⟨x, hx, rfl⟩
    exact mem_inf.mpr ⟨S.hLn g hgH x (mem_inf.mp hx).1,
      mul_mem (mul_mem hgY (mem_inf.mp hx).2) (inv_mem hgY)⟩
  exact eq_of_le_of_card_ge hle (card_map_of_injective (MulAut.conj g).injective).ge

theorem mem_normalizer_LY {g : G} (hg : g ∈ S.Y ⊓ S.H) :
    g ∈ normalizer ((S.L ⊓ S.Y : Subgroup G) : Set G) :=
  mem_normalizer_of_map_eq (S.map_conj_LY hg)

theorem YH_le_frattini (hSy : SylowFacts S.K iX S₀ B) :
    S.Y ⊓ S.H ≤ (S.L ⊓ S.Y) ⊔ (S.Y ⊓ S.H ⊓ normalizer (S.S₀G S₀ : Set G)) := by
  intro g hg
  have hS₀LY : S.S₀G S₀ ≤ S.L ⊓ S.Y :=
    le_inf (S.map_le_L S₀) (fun x hx => (S.S₀G_le hSy hx).1)
  have hS₀2 : IsPGroup 2 (S.S₀G S₀) := hSy.isPGroup.map S.φ
  have hSi : ¬ 2 ∣ (S.S₀G S₀).relIndex (S.L ⊓ S.Y) := by
    rw [S.L_inf_Y, relIndex_map_map_of_injective _ _ S.hφ]
    exact hSy.not_dvd
  have hgLY := S.map_conj_LY hg
  have h1 : (S.S₀G S₀).map (MulAut.conj g).toMonoidHom ≤ S.L ⊓ S.Y := by
    rw [← hgLY]
    exact map_mono hS₀LY
  have h3 : ¬ 2 ∣ ((S.S₀G S₀).map (MulAut.conj g).toMonoidHom).relIndex (S.L ⊓ S.Y) := by
    rw [← hgLY, relIndex_map_map_of_injective _ _ (MulAut.conj g).injective]
    exact hSi
  obtain ⟨c, hc, hcS⟩ := exists_conj_eq_of_sylow h1 (hS₀2.map _) h3 hS₀LY hS₀2 hSi
  have hcomp : (MulAut.conj c).toMonoidHom.comp (MulAut.conj g).toMonoidHom =
      (MulAut.conj (c * g)).toMonoidHom := by
    ext x
    simp [mul_assoc]
  rw [map_map, hcomp] at hcS
  have hcgN : c * g ∈ normalizer (S.S₀G S₀ : Set G) := mem_normalizer_of_map_eq hcS
  have hcYH : c ∈ S.Y ⊓ S.H := mem_inf.mpr ⟨(mem_inf.mp hc).2, S.hLH (mem_inf.mp hc).1⟩
  have : g = c⁻¹ * (c * g) := by group
  rw [this]
  exact mul_mem_sup (inv_mem hc) (mem_inf.mpr ⟨mul_mem hcYH hg, hcgN⟩)

theorem LY_le (hF1 : F1) : S.L ⊓ S.Y ≤ S.K₃ ⊔ S.M := by
  have h := (hF1 S.K S.odd_card (S.hK ▸ S.h5)).2
  have hO : ((pPrimeCore 2 ↥(centralizer ({qThree S.K} : Set S.X))).map
      (centralizer ({qThree S.K} : Set S.X)).subtype).map S.φ = S.K₃ := by
    rw [map_oddCore S.φ S.hφ, ← S.L_inf_Y]
  have hN : (centralizer ({qThree S.K} : Set S.X) ⊓
      normalizer (fourT S.K : Set S.X)).map S.φ ≤ S.M := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 := (S.map_centralizer (qThree S.K)).le ⟨x, (mem_inf.mp hx).1, rfl⟩
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨(mem_inf.mp h1).2,
      S.map_normalizer_le ⟨x, (mem_inf.mp hx).2, rfl⟩⟩, S.hLH (mem_inf.mp h1).1⟩
  rw [S.L_inf_Y]
  calc (centralizer ({qThree S.K} : Set S.X)).map S.φ ≤ (oddCoreOf (centralizer
        ({qThree S.K} : Set S.X)) ⊔ (centralizer ({qThree S.K} : Set S.X) ⊓
          normalizer (fourT S.K : Set S.X))).map S.φ := map_mono h
    _ = _ := map_sup _ _ _
    _ ≤ S.K₃ ⊔ S.M := sup_le_sup (le_of_eq hO) hN

theorem K₃_le_K (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) :
    S.K₃ ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := S.le_sup_oddCore hI hSy
  have hK₃Y : S.K₃ ≤ S.Y := (map_subtype_le _).trans inf_le_right
  have htop : pPrimeCore 2 ↥S.Y ⊔ (S.Y ⊓ S.H).subgroupOf S.Y = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have h' : y ∈ ((pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ (S.Y ⊓ S.H)).subgroupOf S.Y :=
      mem_subgroupOf.mpr (hY y.2)
    rw [subgroupOf_sup (map_subtype_le _) inf_le_left] at h'
    have e : ((pPrimeCore 2 ↥S.Y).map S.Y.subtype).subgroupOf S.Y = pPrimeCore 2 ↥S.Y :=
      comap_map_eq_self_of_injective S.Y.subtype_injective _
    rwa [e] at h'
  have hK₀ : ∀ c ∈ (S.Y ⊓ S.H).subgroupOf S.Y, ∀ k ∈ S.K₃.subgroupOf S.Y,
      c * k * c⁻¹ ∈ S.K₃.subgroupOf S.Y := by
    intro c hc k hk
    rw [mem_subgroupOf] at hc hk ⊢
    simp only [coe_mul, coe_inv]
    exact CFSG.Walter.conj_mem_map_of_characteristic (S.mem_normalizer_LY hc) hk
  have hodd : Odd (Nat.card ↥(S.K₃.subgroupOf S.Y)) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hK₃Y).toEquiv,
      card_map_of_injective (subtype_injective _)]
    exact Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have h := le_pPrimeCore_of_sup_eq_top htop hK₀ hodd
  intro x hx
  exact ⟨⟨x, hK₃Y hx⟩, h (mem_subgroupOf.mpr hx), rfl⟩

theorem le_K_sup_M (hF1 : F1) (hI : IBarFacts S.K S.p iX) (hSy : SylowFacts S.K iX S₀ B) :
    S.Y ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ S.M := by
  have hN : S.Y ⊓ S.H ⊓ normalizer (S.S₀G S₀ : Set G) ≤ S.M := by
    intro m hm
    obtain ⟨hmYH, hmN⟩ := mem_inf.mp hm
    obtain ⟨hmY, hmH⟩ := mem_inf.mp hmYH
    exact mem_inf.mpr ⟨mem_inf.mpr ⟨hmY,
      S.mem_normalizer_T_of_normalizer_S₀ hSy hI hmH hmN⟩, hmH⟩
  have h2 : S.Y ⊓ S.H ≤ S.K₃ ⊔ S.M :=
    (S.YH_le_frattini hSy).trans (sup_le (S.LY_le hF1) (hN.trans le_sup_right))
  have h3 := S.K₃_le_K hI hSy
  calc S.Y ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ (S.Y ⊓ S.H) := S.le_sup_oddCore hI hSy
    _ ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ (S.K₃ ⊔ S.M) := sup_le_sup_left h2 _
    _ ≤ (pPrimeCore 2 ↥S.Y).map S.Y.subtype ⊔ S.M :=
        sup_le le_sup_left (sup_le (h3.trans le_sup_left) le_sup_right)

end Setup

end CFSG.ComponentClassification.HarrisLit.T1.S74
