module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115AutTransport
public import CFSG.Sporadic.Schreier.MathieuOddCoreM11
public import CFSG.Sporadic.Schreier.MathieuOddCoreM12Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Outer
public import CFSG.Sporadic.Schreier.MathieuOddCoreM23
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native
  CFSG.ComponentClassification.OuterAutomorphisms

section Cosets

variable {M : Type*} [Group M]

theorem centralizer_card_of_reps {n : ℕ} (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {gens gensInv : Array Table} {gg : ℕ → Equiv.Perm (Fin n)}
    (hg : ∀ l < gens.size,
      Rep n gens[l]! (gg l) ∧ Rep n gensInv[l]! (gg l)⁻¹ ∧ gg l ∈ Q.originalSubgroup)
    (g₀ : Equiv.Perm (Fin n))
    (hg₀ : ∀ h ∈ Q.originalSubgroup, g₀⁻¹ * h * g₀ ∈ Q.originalSubgroup)
    (data : List (Equiv.Perm (Fin n) × Subgroup (Equiv.Perm (Fin n))))
    (hreps : ∀ d ∈ data, g₀⁻¹ * d.1 ∈ Q.originalSubgroup ∧ orderOf d.1 = 2) (cap : ℕ)
    (hok : repsOK n gens gensInv (cosetOrderTables Q g₀ 2) (data.map fun d => toTable d.1) cap =
      true)
    (hK : ∀ d ∈ data, d.2 ≤ centralizerIn Q.originalSubgroup d.1 ∧
      (conjClosure n gens gensInv (toTable d.1) cap).1.size * Nat.card d.2 =
        Nat.card Q.originalSubgroup) :
    ∀ u, g₀⁻¹ * u ∈ Q.originalSubgroup → orderOf u = 2 →
      ∃ d ∈ data, Nat.card (centralizerIn Q.originalSubgroup u) = Nat.card d.2 := by
  have hok' : repsOK n gens gensInv (cosetOrderTables Q g₀ 2)
      ((data.map Prod.fst).map toTable) cap = true := by
    rw [List.map_map]
    exact hok
  obtain ⟨hcov, hsize⟩ := exists_conj_of_repsOK hn Q hQ hg g₀ hg₀ (by norm_num)
    (data.map Prod.fst) (fun r hr => by
      obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
      exact hreps d hd) cap hok'
  intro u hu ho
  obtain ⟨r, hr, c, hc, rfl⟩ := hcov u hu ho
  obtain ⟨d, hd, rfl⟩ := List.mem_map.1 hr
  obtain ⟨hKle, hKcard⟩ := hK d hd
  have hcent := centralizerIn_eq_of_le Q.originalSubgroup d.1 hKle (hsize _ hr) hKcard
  refine ⟨d, hd, ?_⟩
  rw [centralizerIn_conj _ hc, hcent, Subgroup.card_map_of_injective (MulAut.conj c).injective]

theorem outer_fixSub_card (N : Subgroup M) [Finite N] (δ : M)
    (hδ : ∀ h ∈ N, δ * h * δ⁻¹ ∈ N) (hδ2 : δ * δ ∈ N) (hcenter : Subgroup.center N = ⊥)
    (houter : ∀ g ∈ N, ¬∀ h ∈ N, δ * g * h = h * (δ * g))
    (hcard : Nat.card (MulAut N) ≤ 2 * Nat.card N) {S : Set ℕ}
    (hw : ∀ u, δ⁻¹ * u ∈ N → orderOf u = 2 → Nat.card (centralizerIn N u) ∈ S)
    (α : MulAut N) (hα2 : α * α = 1) (hα : α ∉ inner N) : Nat.card (fixSub α) ∈ S := by
  have hδ' := inv_conj_mem N hδ hδ2
  obtain ⟨g, hg, hαg⟩ := exists_eq_conj_of_outer N δ hδ hδ2 hcenter houter hcard α hα
  set u := g * δ
  have hu : δ⁻¹ * u ∈ N := by
    simpa [u, mul_assoc] using hδ' g hg
  have hu2N : u * u ∈ N := by
    have : u * u = g * (δ * g * δ⁻¹) * (δ * δ) := by simp only [u]; group
    rw [this]
    exact N.mul_mem (N.mul_mem hg (hδ g hg)) hδ2
  have hu2 : u * u = 1 := by
    have hc : (⟨u * u, hu2N⟩ : N) ∈ Subgroup.center N := by
      rw [Subgroup.mem_center_iff]
      intro z
      have hz := congrArg (fun φ : MulAut N => (φ z : M)) hα2
      simp only [MulAut.mul_apply, MulAut.one_apply] at hz
      rw [hαg, hαg] at hz
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      calc (z : M) * (u * u) = u * (u * z * u⁻¹) * u⁻¹ * (u * u) := by rw [hz]
        _ = u * u * z := by group
    rw [hcenter, Subgroup.mem_bot] at hc
    exact congrArg Subtype.val hc
  have hu1 : u ≠ 1 := by
    intro h1
    apply hα
    refine ⟨1, MulEquiv.ext fun z => Subtype.ext ?_⟩
    rw [hαg, h1]
    simp
  have ho : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have hcu := hw u hu ho
  rw [← map_fixSub_conjOn N α u hαg, Subgroup.card_map_of_injective N.subtype_injective] at hcu
  exact hcu

end Cosets

section Transport

variable {K : Type} {N : Type*} [Group K] [Group N]

theorem sylow_card_dvd_fixSub [Finite K] (ψ : K ≃* N) (β : K ≃* K) (P : Sylow 2 K)
    (hP : ∀ t ∈ (P : Subgroup K), β t = t) :
    Nat.card (P : Subgroup K) ∣ Nat.card (fixSub (transAut ψ β)) := by
  have hle : (P : Subgroup K).map ψ.toMonoidHom ≤ fixSub (transAut ψ β) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [mem_fixSub]
    change transAut ψ β (ψ t) = ψ t
    rw [transAut_apply, hP t ht]
  have h1 := Subgroup.card_dvd_of_le hle
  rwa [Subgroup.card_map_of_injective ψ.injective] at h1

theorem sylow_two_card_eq [Finite K] (P : Sylow 2 K) {m : ℕ} (hK : Nat.card K = m) :
    ∃ k i : ℕ, Nat.card (P : Subgroup K) = 2 ^ k ∧ 2 ^ k * i = m ∧ i % 2 = 1 := by
  obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
  refine ⟨k, (P : Subgroup K).index, hk, ?_, ?_⟩
  · rw [← hk, Subgroup.card_mul_index, hK]
  · have := P.not_dvd_index
    omega

theorem autInner_of_equiv_of_inner (ψ : K ≃* N) (h : ∀ α : MulAut N, α ∈ inner N)
    (β : K ≃* K) : IsInnerAut β :=
  isInnerAut_of_transAut_mem_inner ψ β (h _)

theorem autInner_of_equiv_of_outer_card [Finite K] (ψ : K ≃* N) {m : ℕ} (hK : Nat.card K = m)
    {S : Set ℕ}
    (hS : ∀ c ∈ S, ∀ k i : ℕ, 2 ^ k ∣ c → 2 ^ k * i = m → i % 2 = 0)
    (hout : ∀ α : MulAut N, α * α = 1 → α ∉ inner N → Nat.card (fixSub α) ∈ S)
    (β : K ≃* K) (hβ : ∀ x, β (β x) = x) (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) :
    IsInnerAut β := by
  by_cases hin : transAut ψ β ∈ inner N
  · exact isInnerAut_of_transAut_mem_inner ψ β hin
  · exfalso
    obtain ⟨P, hP⟩ := hP
    have hc := hout _ (transAut_mul_self ψ β hβ) hin
    have hd := sylow_card_dvd_fixSub ψ β P hP
    obtain ⟨k, i, hk, hki, hi⟩ := sylow_two_card_eq P hK
    rw [hk] at hd
    have := hS _ hc k i hd hki
    omega

end Transport

section OutTrivial

theorem m11_all_inner
    : ∀ α : MulAut NativeSporadic.M11, α ∈ inner NativeSporadic.M11 := fun α => by
  rw [inner_eq_top_of_card_le m11_center_eq_bot' m11_mulAut_card]
  trivial

theorem m23_all_inner
    : ∀ α : MulAut NativeSporadic.M23, α ∈ inner NativeSporadic.M23 := fun α => by
  rw [inner_eq_top_of_card_le m23_center_eq_bot' m23_mulAut_card]
  trivial

theorem m24_all_inner
    : ∀ α : MulAut NativeSporadic.M24, α ∈ inner NativeSporadic.M24 := fun α => by
  rw [inner_eq_top_of_card_le m24_center_eq_bot' m24_mulAut_card]
  trivial

end OutTrivial

section M22

theorem m22_outer_card
    : ∀ u, m22Delta⁻¹ * u ∈ NativeSporadic.M22 → orderOf u = 2 →
    Nat.card (centralizerIn NativeSporadic.M22 u) = 320 ∨
      Nat.card (centralizerIn NativeSporadic.M22 u) = 1344 := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, hK2, hKc2, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  rw [m22OutReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m22Certificate hQ
    (pairTables_spec hn hA hB) m22Delta hg₀
    [(m22OutRep1, m22OutCentQ1.originalSubgroup), (m22OutRep2, m22OutCentQ2.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩)
    2000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      rcases hd with rfl | rfl
      · refine ⟨hK1, ?_⟩
        dsimp only
        rw [hsz.1, hKc1, m22Certificate_originalSubgroup, m22_card]
      · refine ⟨hK2, ?_⟩
        dsimp only
        rw [hsz.2, hKc2, m22Certificate_originalSubgroup, m22_card])
    u hu ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact Or.inl (hcard.trans hKc1)
  · exact Or.inr (hcard.trans hKc2)

theorem m22_outer_fixSub_card
    (α : MulAut NativeSporadic.M22) (hα2 : α * α = 1)
    (hα : α ∉ inner NativeSporadic.M22) :
    Nat.card (fixSub α) ∈ ({320, 1344} : Set ℕ) :=
  outer_fixSub_card NativeSporadic.M22 m22Delta m22_delta_normalizes m22_delta_sq
    m22_center_eq_bot' m22_delta_outer m22_mulAut_card
    (fun u hu ho => by simpa using m22_outer_card u hu ho) α hα2 hα

end M22

section M12

theorem m12D_outer_card
    : ∀ u, m12Sigma⁻¹ * u ∈ m12D.originalSubgroup → orderOf u = 2 →
    Nat.card (centralizerIn m12D.originalSubgroup u) = 120 := by
  have hn : (24 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, hsz, hord⟩ := m12_sigma_cover
  obtain ⟨hc, ho, hcomm, -⟩ := m12_sigma_cent
  have hA : m12A1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  have hB : m12B1 ∈ m12D.originalSubgroup := m12_gens_memD _ (by simp)
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  have hK : m12SigmaCentQ.originalSubgroup ≤ centralizerIn m12D.originalSubgroup m12Sigma := by
    rw [m12SigmaCentQ, certificate_originalSubgroup]
    exact closure_le_centralizerIn hn (fun g hg => by
      obtain ⟨w, -, rfl⟩ := List.mem_map.1 hg
      exact evalCodes_mem _ m12_gens_memD w) hcomm
  have hKc : Nat.card m12SigmaCentQ.originalSubgroup = 120 := by
    rw [← m12SigmaCentQ.orderCertificate_eq_card hc, ho]
  intro u hu ho2
  obtain ⟨d, hd, hcard⟩ := centralizer_card_of_reps hn m12D m12D_check.1
    (pairTables_spec hn hA hB) m12Sigma (inv_conj_mem _ m12D_sigma_normalizes m12D_sigma_sq)
    [(m12Sigma, m12SigmaCentQ.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨by simp, ?_⟩
      exact (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hord)
    1000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK, ?_⟩
      dsimp only
      rw [hsz, hKc, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2])
    u hu ho2
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact hcard.trans hKc

theorem m12D_outer_fixSub_card
    (α : MulAut m12D.originalSubgroup) (hα2 : α * α = 1)
    (hα : α ∉ inner m12D.originalSubgroup) : Nat.card (fixSub α) ∈ ({120} : Set ℕ) :=
  outer_fixSub_card _ m12Sigma m12D_sigma_normalizes m12D_sigma_sq m12D_center m12D_sigma_outer
    m12D_mulAut_card (fun u hu ho => by simpa using m12D_outer_card u hu ho) α hα2 hα

end M12

@[expose] def IsSporadicResidualName (s : TauCeti.SporadicName) : Prop :=
  s = .J2 ∨ s = .J4 ∨ s = .HS ∨ s = .He ∨ s = .Ru

@[expose] def SporadicResidualAutInner : Prop :=
  ∀ (s : TauCeti.SporadicName), IsSporadicResidualName s → ∀ (K : Type) [Group K] [Finite K],
    Nonempty (K ≃* NativeSporadic.Carrier s) → ∀ β : K ≃* K, (∀ x, β (β x) = x) →
      (∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) → IsInnerAut β

theorem sporadicAutInner_of_residual
    (h : SporadicResidualAutInner) : SporadicAutInner := by
  intro s hs hs1 K _ _ ⟨e⟩ β hβ hP
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact autInner_of_equiv_of_inner e m11_all_inner β
  ·
    let ψ : K ≃* m12D.originalSubgroup := e.trans m12EquivD
    refine autInner_of_equiv_of_outer_card ψ (m := 95040) (S := ({120} : Set ℕ)) ?_ ?_ ?_ β hβ hP
    · rw [Nat.card_congr ψ.toEquiv, ← m12D.orderCertificate_eq_card m12D_check.1, m12D_check.2]
    · intro c hc k i hk hki
      have hc' : c = 120 := by simpa using hc
      subst hc'
      have hk8 : 2 ^ k ≤ 120 := Nat.le_of_dvd (by norm_num) hk
      have hk7 : k < 7 := by
        by_contra hlt
        have : 2 ^ 7 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> omega
    · exact m12D_outer_fixSub_card
  ·
    refine autInner_of_equiv_of_outer_card e (m := 443520) (S := ({320, 1344} : Set ℕ)) ?_ ?_ ?_
      β hβ hP
    · rw [Nat.card_congr e.toEquiv]
      exact m22_card
    · intro c hc k i hk hki
      have hc' : c = 320 ∨ c = 1344 := by simpa using hc
      have hk8 : 2 ^ k ≤ 1344 := by
        rcases hc' with rfl | rfl
        · exact (Nat.le_of_dvd (by norm_num) hk).trans (by norm_num)
        · exact Nat.le_of_dvd (by norm_num) hk
      have hk11 : k < 11 := by
        by_contra hlt
        have : 2 ^ 11 ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases k <;> rcases hc' with rfl | rfl <;> omega
    · intro α hα2 hα
      exact m22_outer_fixSub_card α hα2 hα
  · exact autInner_of_equiv_of_inner e m23_all_inner β
  · exact autInner_of_equiv_of_inner e m24_all_inner β
  · exact absurd rfl hs1
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP
  · exact h _ (by simp [IsSporadicResidualName]) K ⟨e⟩ β hβ hP

end CFSG.QuasithinUnique.Ch1
