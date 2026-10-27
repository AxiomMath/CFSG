module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open CFSG.Blueprint CFSG.LieType.BorelTits

variable {M Γ : Type} [Group M] [Group Γ] {p : ℕ}

theorem WCOn.of_derivedCentralQuotient_noncomm [Finite Γ] [Fact p.Prime] (H : Subgroup M)
    [Finite (DerivedCentralQuotient H)] (e : H ≃* Γ) (h : Holds Γ p) (S : Sylow p Γ)
    (hS : (S : Subgroup Γ) ≤ commutator Γ) {Q : Subgroup Γ} (hQp : IsPGroup p Q)
    (hQ : Q ≤ commutator Γ) {x y : Γ} (hx : x ∈ Q) (hy : y ∈ Q) (hxy : x * y ≠ y * x) :
    WCOn p (DerivedCentralQuotient H) := by
  have hc : Nat.Coprime (Nat.card (Subgroup.center (commutator Γ))) p :=
    (h.of_normal_of_coprime_index (coprime_index_commutator S hS)).coprime_card_center
  let φ : ↥(commutator Γ) →* DerivedCentralQuotient H :=
    (derivedCentralQuotientEquiv H e).symm.toMonoidHom.comp
      (QuotientGroup.mk' (Subgroup.center (commutator Γ)))
  let Q₀ : Subgroup ↥(commutator Γ) := Q.subgroupOf (commutator Γ)
  have hQ₀ : IsPGroup p Q₀ :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQ).symm
  refine WCOn.of_hom_noncomm φ hQ₀ ?_ (x := ⟨x, hQ hx⟩) (y := ⟨y, hQ hy⟩)
    (Subgroup.mem_subgroupOf.2 hx) (Subgroup.mem_subgroupOf.2 hy) ?_
  · intro g hg hφ
    have h1 : QuotientGroup.mk' (Subgroup.center (commutator Γ)) g = 1 := by
      simpa [φ] using hφ
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := hQ₀ ⟨g, hg⟩
    have hgk : g ^ p ^ k = 1 := congrArg Subtype.val hk
    have h2 : orderOf g ∣ Nat.card (Subgroup.center (commutator Γ)) :=
      Subgroup.orderOf_dvd_natCard _ h1
    have h3 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgk
    have h4 : Nat.Coprime (orderOf g) p :=
      Nat.Coprime.coprime_dvd_left h2 hc
    have h5 : orderOf g = 1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k h4) h3
    exact orderOf_eq_one_iff.1 h5
  · intro hne
    apply hxy
    have := congrArg Subtype.val hne
    simpa using this

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
