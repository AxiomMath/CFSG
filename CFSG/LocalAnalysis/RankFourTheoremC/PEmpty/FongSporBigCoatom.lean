module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGenW
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalTransport

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup

@[expose] def CoatomW (X : Type) [Group X] (p : ℕ) : Prop :=
  ∃ (z₀ t : X) (E : Subgroup X), orderOf z₀ = p ∧ IsPGroup 2 E ∧ z₀ ∈ normalizer (E : Set X) ∧
    t ∈ E ∧ t * t = 1 ∧ t ≠ 1 ∧ z₀ * t = t * z₀ ∧ IsCoatom (normalizer (E : Set X)) ∧
    ¬ centralizer ({t} : Set X) ≤ normalizer (E : Set X)

theorem CoatomW.of_mulEquiv {X Y : Type} [Group X] [Group Y] (f : X ≃* Y) {p : ℕ}
    (h : CoatomW X p) : CoatomW Y p := by
  obtain ⟨z₀, t, E, hz, hE, hzE, htE, ht2, ht1, hzt, hco, hnot⟩ := h
  have hN : normalizer ((E.map f.toMonoidHom : Subgroup Y) : Set Y) =
      (normalizer (E : Set X)).map f.toMonoidHom := (map_equiv_normalizer_eq E f).symm
  refine ⟨f z₀, f t, E.map f.toMonoidHom, ?_, hE.map f.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq]
    exact hz
  · rw [hN]
    exact Subgroup.mem_map_of_mem _ hzE
  · exact Subgroup.mem_map_of_mem _ htE
  · rw [← map_mul, ht2, map_one]
  · exact fun h => ht1 (f.injective (by rw [h, map_one]))
  · rw [← map_mul, ← map_mul, hzt]
  · rw [hN]
    exact (OrderIso.isCoatom_iff f.mapSubgroup (normalizer (E : Set X))).mpr hco
  · intro hle
    apply hnot
    intro x hx
    have hfx : f x ∈ centralizer ({f t} : Set Y) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul, hx]
    have := hle hfx
    rw [hN] at this
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
    have hyx' : y = x := f.injective hyx
    rw [← hyx']
    exact hy

theorem false_of_coatomW {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : CoatomW G p) {K : Subgroup G} {z : G}
    (hz : orderOf z = p) (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K) (hK : K ≠ ⊤) : False := by
  obtain ⟨z', t', E', hz', hE', hzE', htE', ht2, ht1, hzt, hco, hnot⟩ := hW
  obtain ⟨g, hg⟩ := exists_conj_zpowers hp hsyl hz hz'
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hg
  let φ : G ≃* G := MulAut.conj g⁻¹
  have hφ : ∀ x : G, φ x = g⁻¹ * x * g := fun x => by simp [φ, MulAut.conj_apply]
  have hzz1 : z ∈ zpowers (φ z') := by
    refine mem_zpowers_iff.mpr ⟨j, ?_⟩
    rw [← map_zpow, hj, hφ]
    group
  have hNE : normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) =
      (normalizer (E' : Set G)).map φ.toMonoidHom := (map_equiv_normalizer_eq E' φ).symm
  have hzt1 : φ z' * φ t' = φ t' * φ z' := by rw [← map_mul, ← map_mul, hzt]
  have hzt2 : z * φ t' = φ t' * z := commute_of_mem_zpowers hzz1 hzt1
  have ht21 : φ t' * φ t' = 1 := by rw [← map_mul, ht2, map_one]
  have ht11 : φ t' ≠ 1 := fun h => ht1 (φ.injective (by rw [h, map_one]))
  have hE1 : IsPGroup 2 (E'.map φ.toMonoidHom) := hE'.map φ.toMonoidHom
  have hzE1 : z ∈ normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) := by
    have h1 : φ z' ∈ normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) := by
      rw [hNE]
      exact Subgroup.mem_map_of_mem _ hzE'
    exact (zpowers_le.mpr h1) hzz1
  have htK : φ t' ∈ K :=
    hN (mem_normalizer_zpowers_of_commute (x := φ t') (t := z) hzt2.symm)
  have hEK : (E'.map φ.toMonoidHom) ⊓ K ≠ ⊥ := by
    intro hbot
    have hmem : φ t' ∈ (E'.map φ.toMonoidHom) ⊓ K :=
      ⟨Subgroup.mem_map_of_mem _ htE', htK⟩
    rw [hbot] at hmem
    exact ht11 (Subgroup.mem_bot.mp hmem)
  have hNK : normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) ≤ K := hcl _ hE1 hzE1 hEK
  have hCK : centralizer ({φ t'} : Set G) ≤ K := by
    intro m hm
    rw [Subgroup.mem_centralizer_singleton_iff] at hm
    exact mem_of_centralizes_involution hN hcl ht21 ht11 hzt2 hm
  have hco1 : IsCoatom (normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G)) := by
    rw [hNE]
    exact (OrderIso.isCoatom_iff φ.mapSubgroup (normalizer (E' : Set G))).mpr hco
  have hnot1 : ¬ centralizer ({φ t'} : Set G) ≤
      normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) := by
    intro hle
    apply hnot
    intro x hx
    have hfx : φ x ∈ centralizer ({φ t'} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← map_mul, ← map_mul, hx]
    have := hle hfx
    rw [hNE] at this
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
    have hyx' : y = x := φ.injective hyx
    rw [← hyx']
    exact hy
  have hlt : normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) <
      normalizer ((E'.map φ.toMonoidHom : Subgroup G) : Set G) ⊔ centralizer ({φ t'} : Set G) :=
    lt_of_le_of_ne le_sup_left (fun h => hnot1 (calc
      centralizer ({φ t'} : Set G) ≤ _ ⊔ centralizer ({φ t'} : Set G) := le_sup_right
      _ = _ := h.symm))
  have htop := hco1.2 _ hlt
  exact hK (top_le_iff.mp (htop ▸ sup_le hNK hCK))

theorem row_of_coatomW {s : TauCeti.SporadicName} {p : ℕ} (X : Type) [Group X]
    (hX : ∀ (G : Type) [Group G],
      Nonempty (G ≃* (TauCeti.CFSGIndex.sporadic s).Group) → Nonempty (G ≃* X))
    (hsyl : ¬ p ^ 2 ∣ Nat.card X) (hW : CoatomW X p) : KFactSporLocalRow s p := by
  apply row_of_model
  intro G _ _ ⟨e'⟩ hp hp5 K z hz hK hzK hN hcl hy hNN
  obtain ⟨φ⟩ := hX G ⟨e'⟩
  have hsylG : ¬ p ^ 2 ∣ Nat.card G := by
    rw [Nat.card_congr φ.toEquiv]
    exact hsyl
  exact (false_of_coatomW hp hsylG (CoatomW.of_mulEquiv φ.symm hW) hz hN hcl hK).elim

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
