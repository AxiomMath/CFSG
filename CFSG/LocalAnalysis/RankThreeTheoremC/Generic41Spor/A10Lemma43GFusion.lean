module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Case2K0
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Lemma43GDefs

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3 (u3S u3T u3K0)

theorem a10t1_lift_conj {H : Type*} [Group H] [Finite H] {p : ℕ} [Fact p.Prime]
    (O : Subgroup H) [O.Normal] {S : Subgroup H} (hS : IsSylowOf p S ⊤) {a : H}
    (ha : IsPGroup p (Subgroup.zpowers a)) (g : H)
    (hg : (Subgroup.zpowers (QuotientGroup.mk' O a)).map
        (MulAut.conj (QuotientGroup.mk' O g)).toMonoidHom ≤ S.map (QuotientGroup.mk' O)) :
    ∃ g' : H, QuotientGroup.mk' O g' = QuotientGroup.mk' O g ∧ g' * a * g'⁻¹ ∈ S := by
  set π := QuotientGroup.mk' O with hπ
  set K : Subgroup H := (S.map π).comap π with hK
  have hSK : S ≤ K := Subgroup.le_comap_map π S
  set Q : Subgroup H := (Subgroup.zpowers a).map (MulAut.conj g).toMonoidHom with hQ
  have hQp : IsPGroup p Q := ha.map _
  have hQK : Q ≤ K := by
    intro q hq
    obtain ⟨y, hy, rfl⟩ := hq
    have hy' : π y ∈ Subgroup.zpowers (π a) := by
      rw [← MonoidHom.map_zpowers]
      exact Subgroup.mem_map_of_mem π hy
    have : π ((MulAut.conj g).toMonoidHom y) ∈
        (Subgroup.zpowers (π a)).map (MulAut.conj (π g)).toMonoidHom :=
      ⟨π y, hy', by simp⟩
    exact hg this
  have hSsyl : IsSylowOf p S K := hS.of_le hSK le_top
  obtain ⟨T, hT⟩ := (hQp.comap_subtype (K := K)).exists_le_sylow
  have hTsyl : IsSylowOf p ((T : Subgroup K).map K.subtype) K := ⟨T, rfl⟩
  have hQT : Q ≤ (T : Subgroup K).map K.subtype := by
    intro q hq
    exact ⟨⟨q, hQK hq⟩, hT (show (⟨q, hQK hq⟩ : K) ∈ Q.comap K.subtype from hq), rfl⟩
  obtain ⟨k, hkK, hk⟩ := hSsyl.exists_mem_conj hTsyl
  obtain ⟨p₁, hp₁, hp₁k⟩ := hkK
  set r : H := k * p₁⁻¹ with hr
  have hrO : π r = 1 := by simp [hr, hp₁k]
  have h1 : g * a * g⁻¹ ∈ (T : Subgroup K).map K.subtype :=
    hQT ⟨a, Subgroup.mem_zpowers a, by simp⟩
  have h2 : k⁻¹ * (g * a * g⁻¹) * k ∈ S := (hk _).mp h1
  have h3 : (r⁻¹ * g) * a * (r⁻¹ * g)⁻¹ ∈ S := by
    have : (r⁻¹ * g) * a * (r⁻¹ * g)⁻¹ = p₁ * (k⁻¹ * (g * a * g⁻¹) * k) * p₁⁻¹ := by
      simp only [hr]; group
    rw [this]
    exact S.mul_mem (S.mul_mem hp₁ h2) (S.inv_mem hp₁)
  refine ⟨r⁻¹ * g, ?_, h3⟩
  simp [map_mul, map_inv, hrO]

variable {G : Type} [Group G] [Finite G] {P : Sylow 5 G} {M : Subgroup G} {x : G} {J : Subgroup G}

theorem a10t1_map_conj_eq {Y : Type*} [Group Y] (π : ↥M →* Y) (u v g : ↥M)
    (h : (Subgroup.zpowers (u : G)).map (MulAut.conj (g : G)).toMonoidHom = Subgroup.zpowers (v : G)) :
    (Subgroup.zpowers (π u)).map (MulAut.conj (π g)).toMonoidHom = Subgroup.zpowers (π v) := by
  rw [MonoidHom.map_zpowers] at h
  have h' : Subgroup.zpowers (g * u * g⁻¹) = Subgroup.zpowers v := by
    apply Subgroup.map_injective M.subtype_injective
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    simpa using h
  rw [MonoidHom.map_zpowers]
  have h1 : (MulAut.conj (π g)).toMonoidHom (π u) = π (g * u * g⁻¹) := by simp
  rw [h1, ← MonoidHom.map_zpowers, h', MonoidHom.map_zpowers]

theorem a10_fusion_Y (hc : PointConfig IsA10Type G 5 P M x J) {Q : Type} [Group Q] [Finite Q] (ψ : ↥J →* Q)
    (hB : A10StageB P x J ψ) (hxM : x ∈ M) {a₁ a₂ : G} (ha₁M : a₁ ∈ M) (ha₂M : a₂ ∈ M)
    (hfive : ∀ A : Subgroup G, IsFiveCycleLine J (u3T P x J) ψ A →
      A = Subgroup.zpowers a₁ ∨ A = Subgroup.zpowers a₂) :
    ∀ y : A10Y M, (Subgroup.zpowers (a10π M ⟨x, hxM⟩)).map (MulAut.conj y).toMonoidHom ≤
        a10Img M (P : Subgroup G) →
      (Subgroup.zpowers (a10π M ⟨x, hxM⟩)).map (MulAut.conj y).toMonoidHom =
          Subgroup.zpowers (a10π M ⟨x, hxM⟩) ∨
        (Subgroup.zpowers (a10π M ⟨x, hxM⟩)).map (MulAut.conj y).toMonoidHom =
          Subgroup.zpowers (a10π M ⟨a₁, ha₁M⟩) ∨
        (Subgroup.zpowers (a10π M ⟨x, hxM⟩)).map (MulAut.conj y).toMonoidHom =
          Subgroup.zpowers (a10π M ⟨a₂, ha₂M⟩) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro y hy
  have hxP : x ∈ (P : Subgroup G) := hc.generic.1
  have hPM : (P : Subgroup G) ≤ M := by
    have h3 : 3 ≤ CFSG.Open.pRank 5 (P : Subgroup G) := by
      have h := hc.generic.2.2.2
      have h' := CFSG.RankThreeCoreUniqueness.Helpers.pRank_mono 5 (by norm_num)
        (inf_le_left : (P : Subgroup G) ⊓ Subgroup.centralizer ({x} : Set G) ≤ P)
      omega
    exact (sylowGroup_le_aschCore 2 5 (P : Subgroup G) (by omega) h3).trans hc.core.2
  have hPsyl : IsSylowOf 5 ((P : Subgroup G).subgroupOf M) ⊤ := by
    rw [isSylowOf_iff]
    refine ⟨le_top, P.isPGroup'.comap_subtype, ?_⟩
    intro hdvd
    rw [Subgroup.relIndex_top_right] at hdvd
    exact P.not_dvd_index (hdvd.trans (Subgroup.relIndex_dvd_index_of_le hPM))
  have ha : IsPGroup 5 (Subgroup.zpowers (⟨x, hxM⟩ : ↥M)) := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp P.isPGroup') ⟨x, hxP⟩
    refine IsPGroup.of_card (n := k) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, ← Subgroup.orderOf_mk x hxP]
    exact hk
  obtain ⟨g₁, rfl⟩ := QuotientGroup.mk'_surjective (primeComplementCore (G := ↥M) 5) y
  obtain ⟨g', hg', hg'P⟩ := a10t1_lift_conj (primeComplementCore (G := ↥M) 5) hPsyl ha g₁ hy
  have hg'P' : (g' : G) * x * (g' : G)⁻¹ ∈ (P : Subgroup G) := by
    simpa [Subgroup.mem_subgroupOf] using hg'P
  have hAmem : (Subgroup.zpowers x).map (MulAut.conj (g' : G)).toMonoidHom ∈
      conjLines x (P : Subgroup G) := by
    refine ⟨(g' : G), rfl, ?_⟩
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_le]
    simpa using hg'P'
  have hcases : (Subgroup.zpowers x).map (MulAut.conj (g' : G)).toMonoidHom = Subgroup.zpowers x ∨
      (Subgroup.zpowers x).map (MulAut.conj (g' : G)).toMonoidHom = Subgroup.zpowers a₁ ∨
      (Subgroup.zpowers x).map (MulAut.conj (g' : G)).toMonoidHom = Subgroup.zpowers a₂ := by
    rcases hB.2 with h | ⟨A₁, A₂, -, h₁, h₂, h⟩
    · rw [h] at hAmem
      exact Or.inl hAmem
    · rw [h] at hAmem
      rcases hAmem with h0 | h0 | h0
      · exact Or.inl h0
      · rcases hfive A₁ h₁ with h' | h'
        · exact Or.inr (Or.inl (h0.trans h'))
        · exact Or.inr (Or.inr (h0.trans h'))
      · rcases hfive A₂ h₂ with h' | h'
        · exact Or.inr (Or.inl (h0.trans h'))
        · exact Or.inr (Or.inr (h0.trans h'))
  rw [← hg']
  rcases hcases with h | h | h
  · exact Or.inl (a10t1_map_conj_eq (a10π M) ⟨x, hxM⟩ ⟨x, hxM⟩ g' h)
  · exact Or.inr (Or.inl (a10t1_map_conj_eq (a10π M) ⟨x, hxM⟩ ⟨a₁, ha₁M⟩ g' h))
  · exact Or.inr (Or.inr (a10t1_map_conj_eq (a10π M) ⟨x, hxM⟩ ⟨a₂, ha₂M⟩ g' h))

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
