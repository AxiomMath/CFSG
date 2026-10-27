module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.CrownLemmaBasic
public import CFSG.LocalAnalysis.LyonsUnitaryFour.Fusion

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37

variable {G : Type*} [Group G]

theorem exists_pow_eq_one_mem_normalizer_not_mem [Finite G] {p : ℕ} [Fact p.Prime]
    {K E H : Subgroup G} (hEK : E ≤ K) (hE : IsPGroup p E) (hHK : H ≤ K) (hH : IsPGroup p H)
    (hcard : Nat.card E < Nat.card H) :
    ∃ r ∈ K, r ∉ E ∧ r ∈ Subgroup.normalizer (E : Set G) ∧ ∃ k : ℕ, r ^ p ^ k = 1 := by
  have hE' : IsPGroup p (E.subgroupOf K) := hE.of_equiv (Subgroup.subgroupOfEquivOfLe hEK).symm
  have hH' : IsPGroup p (H.subgroupOf K) := hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  obtain ⟨P, hP⟩ := hE'.exists_le_sylow
  obtain ⟨Q, hQ⟩ := hH'.exists_le_sylow
  have hcardE : Nat.card (E.subgroupOf K) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hcardH : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv
  have hPQ : Nat.card P = Nat.card Q := by
    rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity]
  have hHQ : Nat.card (H.subgroupOf K) ≤ Nat.card Q := Subgroup.card_le_of_le hQ
  have hne : (E.subgroupOf K).subgroupOf P ≠ ⊤ := by
    intro htop
    have hle : (P : Subgroup K) ≤ E.subgroupOf K := fun x hx => by
      have : (⟨x, hx⟩ : P) ∈ (E.subgroupOf K).subgroupOf P := htop ▸ Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
    have := Subgroup.card_le_of_le hle
    omega
  have : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hlt := Group.normalizerCondition_of_isNilpotent _ (lt_top_iff_ne_top.2 hne)
  obtain ⟨x, hxN, hxE⟩ := IsConcreteLE.exists_of_lt hlt
  have hxN' : (x : K) ∈ Subgroup.normalizer ((E.subgroupOf K : Subgroup K) : Set K) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hP] at hxN
    exact Subgroup.mem_subgroupOf.1 hxN
  have hxN'' : ((x : K) : G) ∈ Subgroup.normalizer (E : Set G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hEK] at hxN'
    exact Subgroup.mem_subgroupOf.1 hxN'
  refine ⟨((x : K) : G), (x : K).2, fun hxE' => hxE ?_, hxN'', ?_⟩
  · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_subgroupOf.2 hxE')
  · obtain ⟨k, hk⟩ := P.isPGroup' x
    exact ⟨k, by simpa using congrArg (fun z : P => ((z : K) : G)) hk⟩

theorem mem_centralizer_of_mem_normalizer_of_sylow_le [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {D : Subgroup G} (hSD : (S : Subgroup G) ≤ Subgroup.centralizer (D : Set G))
    {t : G} (ht : t ∈ Subgroup.normalizer (D : Set G)) (htp : ∃ k : ℕ, t ^ p ^ k = 1) :
    t ∈ Subgroup.centralizer (D : Set G) := by
  obtain ⟨m, hmN, hmt⟩ := LyonsUnitaryFour.exists_conj_mem_sylow_of_le S
    (hSD.trans (Subgroup.centralizer_le_normalizer _)) ht htp
  refine Subgroup.mem_centralizer_iff.2 fun x hx => ?_
  have hmx : m * x * m⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.1 hmN x).1 hx
  have hc := Subgroup.mem_centralizer_iff.1 (hSD hmt) _ hmx
  have h1 : m * (x * t) * m⁻¹ = m * (t * x) * m⁻¹ := by
    calc m * (x * t) * m⁻¹ = m * x * m⁻¹ * (m * t * m⁻¹) := by group
      _ = m * t * m⁻¹ * (m * x * m⁻¹) := hc
      _ = m * (t * x) * m⁻¹ := by group
  simpa using h1

namespace CrownSetting

variable {W : Subgroup G} {y : G}

theorem exists_conj_mem_axis [Finite G] {S : Sylow 2 G} (h : CrownSetting (S : Subgroup G) W y)
    (hcard : 2 * Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) < Nat.card W) {g : G}
    (hg : g⁻¹ * y * g ∈ W) :
    ∃ n ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ Subgroup.centralizer {y} : Subgroup G) :
      Set G), n * y * n⁻¹ ∈ W ⊓ Subgroup.centralizer {y} := by
  have hHC : W.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer {y} := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hc := h.comm hw hg
    calc g * w * g⁻¹ * y = g * (w * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * (g⁻¹ * y * g * w) * g⁻¹ := by rw [hc]
      _ = y * (g * w * g⁻¹) := by group
  have hWp : IsPGroup 2 W := fun w => ⟨1, Subtype.ext (by simpa using h.sq_eq_one w w.2)⟩
  have hlt : Nat.card ((S : Subgroup G) ⊓ Subgroup.centralizer {y} : Subgroup G) <
      Nat.card (W.map (MulAut.conj g).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact h.card_le.trans_lt hcard
  obtain ⟨r, hrC, hrE, hrN, hrp⟩ := exists_pow_eq_one_mem_normalizer_not_mem inf_le_right
    (S.isPGroup'.to_le inf_le_left) hHC (hWp.map _) hlt
  obtain ⟨n, hnN, hnr⟩ := LyonsUnitaryFour.exists_conj_mem_sylow_of_le S h.le_normalizer hrN hrp
  have hnE := Subgroup.mem_normalizer_iff.1 hnN
  have hry : r * y = y * r := Subgroup.mem_centralizer_singleton_iff.1 hrC
  refine ⟨n, hnN, h.mem_axis_of_commute hnr (fun hs => hrE ((hnE r).2 hs)) ((hnE y).1 h.y_mem) ?_⟩
  calc n * r * n⁻¹ * (n * y * n⁻¹) = n * (r * y) * n⁻¹ := by group
    _ = n * (y * r) * n⁻¹ := by rw [hry]
    _ = n * y * n⁻¹ * (n * r * n⁻¹) := by group

theorem false_of_conj_mem_axis [Finite G] {S : Sylow 2 G} (h : CrownSetting (S : Subgroup G) W y)
    (hW : Nat.card W = Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G) ^ 2)
    (hΔ : 2 < Nat.card (W ⊓ Subgroup.centralizer {y} : Subgroup G)) {n : G}
    (hnN : n ∈ Subgroup.normalizer (((S : Subgroup G) ⊓ Subgroup.centralizer {y} : Subgroup G) :
      Set G)) (hy₁ : n * y * n⁻¹ ∈ W ⊓ Subgroup.centralizer {y}) : False := by
  set Δ : Subgroup G := W ⊓ Subgroup.centralizer {y}
  obtain ⟨ℓ, hℓΔ, hℓ1, hnℓ⟩ := h.exists_ne_one_mem_axis hΔ hnN hy₁
  obtain ⟨τ, hτW, hτ⟩ := h.exists_conj_eq hW hℓΔ
  have hτ2 : τ * τ = 1 := by rw [← sq]; exact h.sq_eq_one τ hτW
  have ht2 : n * τ * n⁻¹ * (n * τ * n⁻¹) = 1 := by
    rw [show n * τ * n⁻¹ * (n * τ * n⁻¹) = n * (τ * τ) * n⁻¹ by group, hτ2]
    group
  have htN : n * τ * n⁻¹ ∈ Subgroup.normalizer (Δ : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    refine fun x => ⟨h.conj_mem_axis hnN hτW hτ hnℓ, fun hx => ?_⟩
    have hx' := h.conj_mem_axis hnN hτW hτ hnℓ hx
    rwa [show n * τ * n⁻¹ * (n * τ * n⁻¹ * x * (n * τ * n⁻¹)⁻¹) * (n * τ * n⁻¹)⁻¹ =
        (n * τ * n⁻¹ * (n * τ * n⁻¹)) * x * (n * τ * n⁻¹ * (n * τ * n⁻¹))⁻¹ by group, ht2,
      one_mul, inv_one, mul_one] at hx'
  have hSC : (S : Subgroup G) ≤ Subgroup.centralizer (Δ : Set G) := fun s hs =>
    Subgroup.mem_centralizer_iff.2 fun x hx => h.axis_comm hx hs
  have htC := mem_centralizer_of_mem_normalizer_of_sylow_le S hSC htN
    ⟨1, by rw [pow_one, sq]; exact ht2⟩
  have hcomm := Subgroup.mem_centralizer_iff.1 htC _ hy₁
  apply hℓ1
  have h1 : n * (τ * y * τ⁻¹) * n⁻¹ = n * y * n⁻¹ := by
    rw [show n * (τ * y * τ⁻¹) * n⁻¹ =
        n * τ * n⁻¹ * (n * y * n⁻¹) * (n * τ * n⁻¹)⁻¹ by group, ← hcomm]
    group
  rw [hτ] at h1
  simpa using h1

end CrownSetting

end CFSG.ProperTwoGeneratedCore.Lemma37
