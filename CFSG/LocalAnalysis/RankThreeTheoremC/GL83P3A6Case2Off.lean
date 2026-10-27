module

public import CFSG.Open.LocalVocabulary
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

@[expose] public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Off

open CFSG.Open CFSG.ABGLocalTools Subgroup
open scoped Pointwise

section Elementary

variable {G : Type} [Group G]

theorem elemAbelian_mono {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A) (hBA : B ≤ A) :
    IsElemAbelian p B := by
  haveI := hA.1
  exact ⟨IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    setLike_mul_comm (hBA ha) (hBA hb), fun z hz => hA.2 z (hBA hz)⟩

theorem elemAbelian_sup [Finite G] {p : ℕ} {A B : Subgroup G} (hA : IsElemAbelian p A)
    (hB : IsElemAbelian p B) (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    IsElemAbelian p (A ⊔ B) := by
  haveI := hA.1
  haveI := hB.1
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB
  have hdec : ∀ g ∈ A ⊔ B, ∃ a ∈ A, ∃ b ∈ B, g = a * b := fun g hg => by
    have : g ∈ (A : Set G) * (B : Set G) := by rw [← hset]; exact hg
    obtain ⟨a, ha, b, hb, hab⟩ := this
    exact ⟨a, ha, b, hb, hab.symm⟩
  refine ⟨IsMulCommutative.of_setLike_mul_comm fun u hu v hv => ?_, fun g hg => ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec u hu
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec v hv
    calc a * b * (a' * b') = a * (b * a') * b' := by group
      _ = a * (a' * b) * b' := by rw [hAB a' ha' b hb]
      _ = (a * a') * (b * b') := by group
      _ = (a' * a) * (b' * b) := by
        rw [setLike_mul_comm ha ha', setLike_mul_comm hb hb']
      _ = a' * (a * b') * b := by group
      _ = a' * (b' * a) * b := by rw [hAB a ha b' hb']
      _ = a' * b' * (a * b) := by group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hdec g hg
    rw [(show Commute a b from hAB a ha b hb).mul_pow, hA.2 a ha, hB.2 b hb, one_mul]

theorem offender [Finite G] {Y A W : Subgroup G} (hA : IsElemAbelian 2 A) (hAY : A ≤ Y)
    (hmax : ∀ B : Subgroup G, B ≤ Y → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A)
    (hW : IsElemAbelian 2 W) (hWY : W ≤ Y) :
    Nat.card W * Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) ≤
      Nat.card A * Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := by
  set C : Subgroup G := A ⊓ centralizer (W : Set G) with hC
  have hcomm : ∀ c ∈ C, ∀ w ∈ W, c * w = w * c := fun c hc w hw =>
    (mem_centralizer_iff.mp hc.2 w hw).symm
  have hCel : IsElemAbelian 2 C := elemAbelian_mono hA inf_le_left
  have hel : IsElemAbelian 2 (C ⊔ W) := elemAbelian_sup hCel hW hcomm
  have hle : C ⊔ W ≤ Y := sup_le (inf_le_left.trans hAY) hWY
  have h1 := hmax _ hle hel
  obtain ⟨hprod, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute C W hcomm
  have hCW : (C ⊓ W : Subgroup G) ≤ W ⊓ centralizer (A : Set G) := by
    intro z hz
    haveI := hA.1
    exact ⟨hz.2, mem_centralizer_iff.mpr fun a ha => setLike_mul_comm ha hz.1.1⟩
  have h2 : Nat.card (C ⊓ W : Subgroup G) ≤ Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le hCW
  calc Nat.card W * Nat.card C = Nat.card C * Nat.card W := Nat.mul_comm _ _
    _ = Nat.card (C ⊔ W : Subgroup G) * Nat.card (C ⊓ W : Subgroup G) := hprod.symm
    _ ≤ Nat.card A * Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) :=
      Nat.mul_le_mul h1 h2

end Elementary

section Lift

variable {X : Type} [Group X] [Finite X]

theorem exists_isSylowOf_of_le {p : ℕ} [Fact p.Prime] {S K : Subgroup X} (hS : IsPGroup p S)
    (hSK : S ≤ K) : ∃ P : Subgroup X, IsSylowOf p P K ∧ S ≤ P := by
  obtain ⟨Q, hQ⟩ := (hS.comap_subtype (K := K)).exists_le_sylow
  exact ⟨(Q : Subgroup K).map K.subtype, ⟨Q, rfl⟩, fun s hs => ⟨⟨s, hSK hs⟩, hQ hs, rfl⟩⟩

theorem isPGroup_zpowers_three {x : X} (hx3 : x ^ 3 = 1) : IsPGroup 3 (zpowers x) := by
  rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hx3) with h | h
  · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h]; rfl)
  · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h]; rfl)

theorem lift_three_abs {K D : Subgroup X} [K.Normal] (hK : ¬ 3 ∣ Nat.card K) {x : X}
    (hx3 : x ^ 3 = 1) (hx : x ∈ D ⊔ K) : ∃ κ ∈ K, ∃ x' ∈ D, x = κ * x' * κ⁻¹ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf (G := X) 3 D
  set Z : Subgroup X := D ⊔ K with hZ
  have hSZ : IsSylowOf 3 S Z := by
    rw [isSylowOf_iff]
    refine ⟨hS.le.trans le_sup_left, hS.isPGroup, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex S D Z hS.le le_sup_left]
    intro hdvd
    have hSD : ¬ 3 ∣ S.relIndex D := (isSylowOf_iff.mp hS).2.2
    have hDK : D.relIndex K ∣ Nat.card K := Subgroup.relIndex_dvd_card D K
    have hDZ : ¬ 3 ∣ D.relIndex Z := by
      have h1 : D.relIndex (K ⊔ D) = D.relIndex K := relIndex_sup_eq_relIndex_of_normal K D
      rw [hZ, sup_comm, h1]
      exact fun h3 => hK (h3.trans hDK)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp hdvd with h | h
    · exact hSD h
    · exact hDZ h
  obtain ⟨P', hP', hxP'⟩ := exists_isSylowOf_of_le (p := 3) (isPGroup_zpowers_three hx3)
    (zpowers_le.mpr hx : zpowers x ≤ Z)
  obtain ⟨k, hkZ, hk⟩ := hSZ.exists_mem_conj hP'
  obtain ⟨κ, hκ, d, hd, hkd⟩ : ∃ κ ∈ K, ∃ d ∈ D, k = κ * d := by
    have : k ∈ (K : Set X) * (D : Set X) := by
      rw [← Subgroup.normal_mul, sup_comm]
      exact hkZ
    obtain ⟨κ, hκ, d, hd, h⟩ := this
    exact ⟨κ, hκ, d, hd, h.symm⟩
  have hxS : k⁻¹ * x * k ∈ S := (hk x).mp (hxP' (mem_zpowers x))
  refine ⟨κ, hκ, d * (k⁻¹ * x * k) * d⁻¹, ?_, ?_⟩
  · exact D.mul_mem (D.mul_mem hd (hS.le hxS)) (D.inv_mem hd)
  · rw [hkd]; group

end Lift

theorem lift_three {G : Type} [Group G] [Finite G] {H K D : Subgroup G} (hKH : K ≤ H)
    (hDH : D ≤ H) (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) (hK : ¬ 3 ∣ Nat.card K)
    {x : G} (hxH : x ∈ H) (hx3 : x ^ 3 = 1) (hx : x ∈ D ⊔ K) :
    ∃ κ ∈ K, ∃ x' ∈ D, x = κ * x' * κ⁻¹ := by
  haveI : (K.subgroupOf H).Normal :=
    ⟨fun k hk h => by
      have := hKn h h.2 k (Subgroup.mem_subgroupOf.mp hk)
      simpa [Subgroup.mem_subgroupOf] using this⟩
  have hK' : ¬ 3 ∣ Nat.card (K.subgroupOf H) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKH).toEquiv]
  have hx3' : (⟨x, hxH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx' : (⟨x, hxH⟩ : H) ∈ D.subgroupOf H ⊔ K.subgroupOf H := by
    rw [← Subgroup.subgroupOf_sup hDH hKH]
    exact hx
  obtain ⟨κ, hκ, x', hx'D, h⟩ := lift_three_abs hK' hx3' hx'
  refine ⟨(κ : G), Subgroup.mem_subgroupOf.mp hκ, (x' : G), Subgroup.mem_subgroupOf.mp hx'D, ?_⟩
  have := congrArg Subtype.val h
  simpa using this

theorem card_le_pow {G : Type} [Group G] [Finite G] {H K W : Subgroup G} {ι : Type} [Fintype ι]
    (B : ι → Subgroup G) (b : ℕ) (hKH : K ≤ H) (hKn : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    (hK3 : ¬ 3 ∣ Nat.card K) (hWH : ∀ h ∈ H, h ∈ normalizer (W : Set G)) (hBH : ∀ i, B i ≤ H)
    (hB : ∀ i, (centralizer (B i : Set G)).relIndex W ≤ b) {x : G} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1) (hx : x ∈ (⨆ i, B i) ⊔ K)
    (hxfix : ∀ w ∈ W, x * w = w * x → w = 1) : Nat.card W ≤ b ^ Fintype.card ι := by
  set D : Subgroup G := ⨆ i, B i with hD
  have hDH : D ≤ H := iSup_le hBH
  obtain ⟨κ, hκ, x', hx'D, hxκ⟩ := lift_three hKH hDH hKn hK3 hxH hx3 hx
  have hE : centralizer (D : Set G) ⊓ W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwC, hwW⟩ := hw
    have hκn : κ ∈ normalizer (W : Set G) := hWH κ (hKH hκ)
    have hw' : κ * w * κ⁻¹ ∈ W := (mem_normalizer_iff.mp hκn w).mp hwW
    have hcomm : x * (κ * w * κ⁻¹) = (κ * w * κ⁻¹) * x := by
      have h1 : x' * w = w * x' := mem_centralizer_iff.mp hwC x' hx'D
      calc x * (κ * w * κ⁻¹) = κ * (x' * w) * κ⁻¹ := by rw [hxκ]; group
        _ = κ * (w * x') * κ⁻¹ := by rw [h1]
        _ = (κ * w * κ⁻¹) * x := by rw [hxκ]; group
    have h1 : κ * w * κ⁻¹ = 1 := hxfix _ hw' hcomm
    have : w = 1 := by
      have h2 : w = κ⁻¹ * (κ * w * κ⁻¹) * κ := by group
      rw [h2, h1]; group
    exact this ▸ one_mem _
  have hcent : centralizer (D : Set G) = ⨅ i, centralizer (B i : Set G) := by
    ext z
    simp only [mem_iInf]
    constructor
    · intro hz i
      exact mem_centralizer_iff.mpr fun d hd =>
        mem_centralizer_iff.mp hz d (le_iSup B i hd)
    · intro hz
      have hle : D ≤ centralizer ({z} : Set G) := iSup_le fun i b hb =>
        mem_centralizer_singleton_iff.mpr (mem_centralizer_iff.mp (hz i) b hb)
      exact mem_centralizer_iff.mpr fun d hd => mem_centralizer_singleton_iff.mp (hle hd)
  have h1 := Subgroup.relIndex_mul_card (centralizer (D : Set G)) W
  rw [hE, Subgroup.card_bot, mul_one] at h1
  rw [← h1, hcent]
  calc (⨅ i, centralizer (B i : Set G)).relIndex W
      ≤ ∏ i, (centralizer (B i : Set G)).relIndex W := Subgroup.relIndex_iInf_le _
    _ ≤ ∏ _i : ι, b := Finset.prod_le_prod' fun i _ => hB i
    _ = b ^ Fintype.card ι := by simp

section Conj

variable {G : Type} [Group G]

theorem centralizer_map_conj (A : Subgroup G) (g : G) :
    centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (centralizer (A : Set G)).map (MulAut.conj g).toMonoidHom := by
  ext z
  simp only [mem_centralizer_iff, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hz
    refine ⟨g⁻¹ * z * g, fun a ha => ?_, by group⟩
    have := hz (g * a * g⁻¹) ⟨a, ha, rfl⟩
    calc a * (g⁻¹ * z * g) = g⁻¹ * ((g * a * g⁻¹) * z) * g := by group
      _ = g⁻¹ * (z * (g * a * g⁻¹)) * g := by rw [this]
      _ = (g⁻¹ * z * g) * a := by group
  · rintro ⟨y, hy, rfl⟩ _ ⟨a, ha, rfl⟩
    have := hy a ha
    calc g * a * g⁻¹ * (g * y * g⁻¹) = g * (a * y) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by rw [this]
      _ = g * y * g⁻¹ * (g * a * g⁻¹) := by group

theorem map_conj_eq_of_mem_normalizer {W : Subgroup G} {g : G}
    (hg : g ∈ normalizer (W : Set G)) : W.map (MulAut.conj g).toMonoidHom = W := by
  ext z
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (mem_normalizer_iff.mp hg y).mp hy
  · intro hz
    refine ⟨g⁻¹ * z * g, ?_, by group⟩
    apply (mem_normalizer_iff.mp hg (g⁻¹ * z * g)).mpr
    rwa [show g * (g⁻¹ * z * g) * g⁻¹ = z by group]

theorem relIndex_centralizer_conj {A W : Subgroup G} {g : G} (hg : g ∈ normalizer (W : Set G)) :
    (centralizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)).relIndex W =
      (centralizer (A : Set G)).relIndex W := by
  rw [centralizer_map_conj]
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (centralizer (A : Set G)) W (MulAut.conj g).injective
  rw [map_conj_eq_of_mem_normalizer hg] at this
  exact this

theorem relIndex_le_of_offender [Finite G] {Y A W K : Subgroup G} (hA : IsElemAbelian 2 A)
    (hAY : A ≤ Y)
    (hmax : ∀ B : Subgroup G, B ≤ Y → IsElemAbelian 2 B → Nat.card B ≤ Nat.card A)
    (hW : IsElemAbelian 2 W) (hWY : W ≤ Y) (hAK : A ⊓ K ≤ centralizer (W : Set G)) :
    (centralizer (A : Set G)).relIndex W ≤ (A ⊓ K).relIndex A := by
  have hoff := offender hA hAY hmax hW hWY
  have h1 := Subgroup.relIndex_mul_card (centralizer (A : Set G)) W
  have h2 := Subgroup.relIndex_mul_card (A ⊓ K) A
  rw [inf_eq_left.mpr (inf_le_left : A ⊓ K ≤ A)] at h2
  rw [inf_comm] at h1
  have h3 : Nat.card (A ⊓ K : Subgroup G) ≤ Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) :=
    Subgroup.card_le_of_le (le_inf inf_le_left hAK)
  have hpos1 : 0 < Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) := Nat.card_pos
  have hpos2 : 0 < Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := Nat.card_pos
  apply Nat.le_of_mul_le_mul_right (c := Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) *
    Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) _ (Nat.mul_pos hpos1 hpos2)
  calc (centralizer (A : Set G)).relIndex W *
        (Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) *
          Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G))
      = ((centralizer (A : Set G)).relIndex W *
          Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) *
          Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) := by ring
    _ = Nat.card W * Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) := by rw [h1]
    _ ≤ Nat.card A * Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := hoff
    _ = (A ⊓ K).relIndex A * Nat.card (A ⊓ K : Subgroup G) *
          Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := by rw [h2]
    _ ≤ (A ⊓ K).relIndex A * Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) *
          Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G) := by
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ h3)
    _ = (A ⊓ K).relIndex A * (Nat.card (A ⊓ centralizer (W : Set G) : Subgroup G) *
          Nat.card (W ⊓ centralizer (A : Set G) : Subgroup G)) := by ring

end Conj

end CFSG.LocalAnalysis.RankThreeTheoremC.GL83P3A6Off
