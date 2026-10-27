module

public import CFSG.Open.RankThreeDefs
import CFSG.Dihedral.DisconnectedInvolutionGraph.PGroupNormalizerExtension
import CFSG.LocalAnalysis.AGLEmbedding.NongenerationTransfer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G]

theorem gen49e_exists_comm [Finite G] {W : Subgroup G} {x : G} (hx : x ∈ normalizer (W : Set G))
    (hfpf : ∀ w ∈ W, w * x = x * w → w = 1) :
    ∀ w ∈ W, ∃ y ∈ W, w = y * x * y⁻¹ * x⁻¹ := by
  have hmem : ∀ y : W, (y : G) * x * (y : G)⁻¹ * x⁻¹ ∈ W := fun y => by
    have h1 : x * (y : G)⁻¹ * x⁻¹ ∈ W := (mem_normalizer_iff.mp hx _).mp (W.inv_mem y.2)
    have h2 := W.mul_mem y.2 h1
    rwa [show (y : G) * (x * (y : G)⁻¹ * x⁻¹) = (y : G) * x * (y : G)⁻¹ * x⁻¹ by group] at h2
  let f : W → W := fun y => ⟨(y : G) * x * (y : G)⁻¹ * x⁻¹, hmem y⟩
  have hinj : Function.Injective f := by
    intro y y' h
    have h1 : (y : G) * x * (y : G)⁻¹ * x⁻¹ = (y' : G) * x * (y' : G)⁻¹ * x⁻¹ :=
      congrArg Subtype.val h
    have h2 : (y : G) * x * (y : G)⁻¹ = (y' : G) * x * (y' : G)⁻¹ := mul_right_cancel h1
    have h3 : ((y' : G)⁻¹ * y) * x = x * ((y' : G)⁻¹ * y) := by
      calc ((y' : G)⁻¹ * y) * x = (y' : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * y := by group
        _ = (y' : G)⁻¹ * ((y' : G) * x * (y' : G)⁻¹) * y := by rw [h2]
        _ = x * ((y' : G)⁻¹ * y) := by group
    have h4 := hfpf _ (W.mul_mem (W.inv_mem y'.2) y.2) h3
    exact Subtype.ext (inv_mul_eq_one.mp h4).symm
  intro w hw
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hinj) ⟨w, hw⟩
  exact ⟨y, y.2, (congrArg Subtype.val hy).symm⟩

theorem gen49e_commutator_mem {H D X W : Subgroup G} (hD : H ≤ normalizer (D : Set G))
    (hX : H ≤ normalizer (X : Set G)) {a : G} (haH : a ∈ H)
    (ha : ∀ k ∈ X, k * a * k⁻¹ * a⁻¹ ∈ D) (hWH : W ≤ H)
    (hWa : ∀ w ∈ W, ∃ y ∈ W, w = y * a * y⁻¹ * a⁻¹) :
    ∀ w ∈ W, ∀ k ∈ X, k * w * k⁻¹ * w⁻¹ ∈ D := by
  have hmul : ∀ u v : G, u ∈ H → (∀ k ∈ X, k * u * k⁻¹ * u⁻¹ ∈ D) →
      (∀ k ∈ X, k * v * k⁻¹ * v⁻¹ ∈ D) → ∀ k ∈ X, k * (u * v) * k⁻¹ * (u * v)⁻¹ ∈ D := by
    intro u v hu hu' hv' k hk
    have e : k * (u * v) * k⁻¹ * (u * v)⁻¹ =
        (k * u * k⁻¹ * u⁻¹) * (u * (k * v * k⁻¹ * v⁻¹) * u⁻¹) := by group
    rw [e]
    exact D.mul_mem (hu' k hk) (le_normalizer_iff.mp hD u hu _ (hv' k hk))
  have hinv : ∀ u : G, u ∈ H → (∀ k ∈ X, k * u * k⁻¹ * u⁻¹ ∈ D) →
      ∀ k ∈ X, k * u⁻¹ * k⁻¹ * u⁻¹⁻¹ ∈ D := by
    intro u hu hu' k hk
    have e : k * u⁻¹ * k⁻¹ * u⁻¹⁻¹ = u⁻¹ * (k * u * k⁻¹ * u⁻¹)⁻¹ * u⁻¹⁻¹ := by group
    rw [e]
    exact le_normalizer_iff.mp hD u⁻¹ (H.inv_mem hu) _ (D.inv_mem (hu' k hk))
  have hconj : ∀ g u : G, g ∈ H → (∀ k ∈ X, k * u * k⁻¹ * u⁻¹ ∈ D) →
      ∀ k ∈ X, k * (g * u * g⁻¹) * k⁻¹ * (g * u * g⁻¹)⁻¹ ∈ D := by
    intro g u hg hu' k hk
    have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ X := le_normalizer_iff.mp hX g⁻¹ (H.inv_mem hg) k hk
    have e : k * (g * u * g⁻¹) * k⁻¹ * (g * u * g⁻¹)⁻¹ =
        g * ((g⁻¹ * k * g⁻¹⁻¹) * u * (g⁻¹ * k * g⁻¹⁻¹)⁻¹ * u⁻¹) * g⁻¹ := by group
    rw [e]
    exact le_normalizer_iff.mp hD g hg _ (hu' _ hk')
  intro w hw k hk
  obtain ⟨y, hy, rfl⟩ := hWa w hw
  have h1 := hconj y a (hWH hy) ha
  have h2 := hinv a haH ha
  have e : y * a * y⁻¹ * a⁻¹ = (y * a * y⁻¹) * a⁻¹ := rfl
  rw [e]
  exact hmul _ _ (H.mul_mem (H.mul_mem (hWH hy) haH) (H.inv_mem (hWH hy))) h1 h2 k hk

theorem gen49e_le_normalizer_sup {H D X W : Subgroup G} (hD : H ≤ normalizer (D : Set G))
    (hXH : X ≤ H) (hW : ∀ w ∈ W, ∀ k ∈ X, k * w * k⁻¹ * w⁻¹ ∈ D) :
    X ≤ normalizer ((D ⊔ W : Subgroup G) : Set G) := by
  refine le_normalizer_iff.mpr fun k hk n hn => ?_
  refine (sup_le (fun d hd => ?_) (fun w hw => ?_) :
    D ⊔ W ≤ (D ⊔ W).comap (MulAut.conj k).toMonoidHom) hn
  · exact mem_sup_left (le_normalizer_iff.mp hD k (hXH hk) d hd)
  · have e : k * w * k⁻¹ = (k * w * k⁻¹ * w⁻¹) * w := by group
    change k * w * k⁻¹ ∈ D ⊔ W
    rw [e]
    exact (D ⊔ W).mul_mem (mem_sup_left (hW w hw k hk)) (mem_sup_right hw)

theorem gen49e_coprime_card_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {Y : Subgroup G} (hY : IsPGroup 2 Y) : Nat.Coprime p (Nat.card Y) := by
  obtain ⟨n, hn⟩ := hY.exists_card_eq
  rw [hn]
  exact ((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow_right n

theorem gen49e_le_primeCore {p : ℕ} {H Z : Subgroup G} (hZH : Z ≤ H)
    (hZ : H ≤ normalizer (Z : Set G)) (hcop : Nat.Coprime p (Nat.card Z)) :
    Z ≤ rankThreePrimeCore p H :=
  le_sSup ⟨hZH, (normal_subgroupOf_iff_le_normalizer hZH).mpr hZ, hcop⟩

theorem gen49e_le_of_inf_le [Finite G] {T Y : Subgroup G} (hT2 : IsPGroup 2 T)
    (hY2 : IsPGroup 2 Y) (hYT : Y ≤ normalizer (T : Set G))
    (hW : T ⊓ normalizer (Y : Set G) ≤ Y) : T ≤ Y := by
  by_contra hnot
  have hJ2 : IsPGroup 2 (Y ⊔ T : Subgroup G) := hY2.to_sup_of_normal_right' hT2 hYT
  have hlt : Y < Y ⊔ T := lt_of_le_of_ne le_sup_left fun h => hnot (h ▸ le_sup_right)
  obtain ⟨E, hYE, -, hE⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.pgroup_strict_normalizer_extension 2 Y _ hJ2 hlt
  obtain ⟨j, hjE, hjY⟩ := IsConcreteLE.exists_of_lt hYE
  have hjJ : j ∈ Y ⊔ T := (mem_inf.mp (hE hjE)).1
  have hjN : j ∈ normalizer (Y : Set G) := (mem_inf.mp (hE hjE)).2
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right Y T hYT] at hjJ
  obtain ⟨y, hy, t, ht, rfl⟩ := hjJ
  have htN : t ∈ normalizer (Y : Set G) := by
    have := (normalizer (Y : Set G)).mul_mem ((normalizer (Y : Set G)).inv_mem
      (le_normalizer hy)) hjN
    rwa [inv_mul_cancel_left] at this
  exact hjY (Y.mul_mem hy (hW ⟨ht, htN⟩))

theorem gen49e_centralizer_le [Finite G] {T Y : Subgroup G} {x : G}
    (hxT : x ∈ normalizer (T : Set G)) (hfpf : ∀ t ∈ T, t * x = x * t → t = 1) (hTY : T ≤ Y)
    (hcomm : ∀ y ∈ Y, y * x * y⁻¹ * x⁻¹ ∈ T) :
    ∀ h ∈ normalizer (Y : Set G), h * x = x * h → h ∈ normalizer (T : Set G) := by
  have key : ∀ h ∈ normalizer (Y : Set G), h * x = x * h → ∀ t ∈ T, h * t * h⁻¹ ∈ T := by
    intro h hh hc t ht
    obtain ⟨y, hy, rfl⟩ := gen49e_exists_comm hxT hfpf t ht
    have hx' : h * x * h⁻¹ = x := by rw [hc, mul_assoc, mul_inv_cancel, mul_one]
    have e : h * (y * x * y⁻¹ * x⁻¹) * h⁻¹ =
        (h * y * h⁻¹) * x * (h * y * h⁻¹)⁻¹ * x⁻¹ := by
      calc h * (y * x * y⁻¹ * x⁻¹) * h⁻¹
          = (h * y * h⁻¹) * (h * x * h⁻¹) * (h * y * h⁻¹)⁻¹ * (h * x * h⁻¹)⁻¹ := by group
        _ = (h * y * h⁻¹) * x * (h * y * h⁻¹)⁻¹ * x⁻¹ := by rw [hx']
    rw [e]
    exact hcomm _ ((mem_normalizer_iff.mp hh y).mp (hTY hy))
  intro h hh hc
  refine mem_normalizer_iff.mpr fun t => ⟨key h hh hc t, fun ht => ?_⟩
  have hh' : h⁻¹ ∈ normalizer (Y : Set G) := inv_mem hh
  have hc' : h⁻¹ * x = x * h⁻¹ := by
    calc h⁻¹ * x = h⁻¹ * (x * h) * h⁻¹ := by group
      _ = h⁻¹ * (h * x) * h⁻¹ := by rw [hc]
      _ = x * h⁻¹ := by group
  have := key h⁻¹ hh' hc' _ ht
  simpa [mul_assoc] using this

theorem gen49e_mem_mul_centralizer [Finite G] {p : ℕ} (hp : p.Prime) {H D : Subgroup G}
    (hDH : D ≤ H) (hHD : H ≤ normalizer (D : Set G)) (hDcop : p.Coprime (Nat.card D))
    {a k : G} (haH : a ∈ H) (hkH : k ∈ H) (hao : orderOf a = p)
    (hk : k * a * k⁻¹ * a⁻¹ ∈ D) :
    ∃ o ∈ D, ∃ c ∈ H, c * a = a * c ∧ o * c = k := by
  have : (D.subgroupOf H).Normal := (normal_subgroupOf_iff_le_normalizer hDH).mpr hHD
  set O := D.subgroupOf H with hO
  have hOcop : p.Coprime (Nat.card O) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv]
    exact hDcop
  set a' : H := ⟨a, haH⟩ with ha'
  set k' : H := ⟨k, hkH⟩ with hk'
  have hao' : orderOf a' = p := by rw [← Subgroup.orderOf_coe a']; exact hao
  have hA : IsPGroup p (zpowers a') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao', pow_one])
  have hc₀ : k' * a' * k'⁻¹ * a'⁻¹ ∈ O := hk
  have h1 : QuotientGroup.mk' O (k' * a' * k'⁻¹ * a'⁻¹) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hc₀
  simp only [map_mul, map_inv] at h1
  have hcomm : QuotientGroup.mk' O a' * QuotientGroup.mk' O k' =
      QuotientGroup.mk' O k' * QuotientGroup.mk' O a' := by
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  have hmem : k' ∈ (centralizer (((zpowers a').map (QuotientGroup.mk' O) : Subgroup (H ⧸ O)) :
      Set (H ⧸ O))).comap (QuotientGroup.mk' O) := by
    rw [Subgroup.mem_comap, MonoidHom.map_zpowers, zpowers_eq_closure, centralizer_closure]
    exact mem_centralizer_iff.mpr fun z hz => by rw [Set.mem_singleton_iff.mp hz]; exact hcomm
  have h2 := CFSG.AGLEmbedding.comap_centralizer_map_le_sup hp O hOcop hA hmem
  obtain ⟨o, ho, c, hc, hoc⟩ := mem_sup_of_normal_left.mp h2
  refine ⟨(o : G), ho, (c : G), c.2, ?_, congrArg Subtype.val hoc⟩
  have := mem_centralizer_iff.mp hc a' (mem_zpowers a')
  exact (congrArg Subtype.val this).symm

end CFSG.LocalAnalysis.RankThreeTheoremC
