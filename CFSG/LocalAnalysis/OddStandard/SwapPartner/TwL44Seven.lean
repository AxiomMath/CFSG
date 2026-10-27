module

public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Excl
public import CFSG.LocalAnalysis.OddStandard.SwapPartner.L44Quotient

public section

namespace CFSG.OddStandard.AltStdSec.SwapPartner

open CFSG.Blueprint Subgroup

theorem dvd_card_inf_of_dvd_centralizer_of_not_dvd_quotient {H : Type*} [Group H] [Finite H]
    (D : Subgroup H) [D.Normal] (d : H) {p : ℕ} (hp : p.Prime)
    (h : p ∣ Nat.card (Subgroup.centralizer ({d} : Set H)))
    (hq : ¬ p ∣ Nat.card (Subgroup.centralizer ({(d : H ⧸ D)} : Set (H ⧸ D)))) :
    p ∣ Nat.card ↥(D ⊓ Subgroup.centralizer ({d} : Set H)) := by
  let C : Subgroup H := Subgroup.centralizer ({d} : Set H)
  change p ∣ Nat.card ↥C at h
  let g : ↥C →* H ⧸ D := (QuotientGroup.mk' D).comp C.subtype
  have hrange_le : g.range ≤ Subgroup.centralizer ({(d : H ⧸ D)} : Set (H ⧸ D)) := by
    rintro _ ⟨c, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hc : (c : H) * d = d * (c : H) :=
      Subgroup.mem_centralizer_singleton_iff.mp c.2
    show (QuotientGroup.mk' D) (c : H) * (d : H ⧸ D) =
      (d : H ⧸ D) * (QuotientGroup.mk' D) (c : H)
    change (QuotientGroup.mk' D) (c : H) * (QuotientGroup.mk' D) d =
      (QuotientGroup.mk' D) d * (QuotientGroup.mk' D) (c : H)
    rw [← map_mul, ← map_mul, hc]
  have hnot : ¬ p ∣ Nat.card ↥g.range := fun hdiv =>
    hq (hdiv.trans (Subgroup.card_dvd_of_le hrange_le))
  have hcard : Nat.card ↥C = Nat.card ↥g.range * Nat.card ↥g.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup g.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange g).toEquiv]
  have hpker : p ∣ Nat.card ↥g.ker := by
    have h' : p ∣ Nat.card ↥g.range * Nat.card ↥g.ker := by
      rw [← hcard]
      exact h
    exact (hp.dvd_mul.mp h').resolve_left hnot
  let φ : ↥g.ker →* ↥(D ⊓ Subgroup.centralizer ({d} : Set H)) :=
    { toFun := fun c => ⟨((c : ↥C) : H), by
        have hc := MonoidHom.mem_ker.mp c.2
        exact ⟨(QuotientGroup.eq_one_iff ((c : ↥C) : H)).mp hc, (c : ↥C).2⟩⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hφinj : Function.Injective φ := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : ↥(D ⊓ Subgroup.centralizer ({d} : Set H)) => (z : H)) hab
  exact hpker.trans (Subgroup.card_dvd_of_injective φ hφinj)

theorem seven_dvd_card_inf_of_perfect {H : Type} [Group H] [Finite H]
    (N D₀ : Subgroup H) [N.Normal] [D₀.Normal] (hN : ⁅N, N⁆ = N)
    (hD : ∀ h : H, h ∈ D₀ ↔ ∀ n ∈ N, h * n = n * h)
    (hS : LieModel (↥N ⧸ Subgroup.center ↥N) .PSL 4 2 2)
    (A : Subgroup (H ⧸ D₀)) (hAS : A ≤ N.map (QuotientGroup.mk' D₀))
    (eA : A ≃* alternatingGroup (Fin 8)) (t : H ⧸ D₀) (d : H)
    (ht1 : t ≠ 1) (ht2 : t * t = 1) (htA : ∀ a ∈ A, t * a = a * t)
    (hd2 : d * d = 1) (hdt : (d : H ⧸ D₀) * t = t * (d : H ⧸ D₀))
    (hdA : ∀ a ∈ A, (d : H ⧸ D₀) * a * (d : H ⧸ D₀)⁻¹ ∈ A)
    (hdout : ¬ ∃ a ∈ A, ∀ x ∈ A, (d : H ⧸ D₀) * x * (d : H ⧸ D₀)⁻¹ = a * x * a⁻¹) :
    7 ∣ Nat.card (centralizer ({d} : Set H)) →
      7 ∣ Nat.card ↥(D₀ ⊓ centralizer ({d} : Set H)) := by
  classical
  let S : Subgroup (H ⧸ D₀) := N.map (QuotientGroup.mk' D₀)
  haveI : S.Normal :=
    Subgroup.Normal.map (H := N) inferInstance (QuotientGroup.mk' D₀)
      (QuotientGroup.mk'_surjective D₀)
  obtain ⟨e⟩ : Nonempty (↥S ≃* (↥N ⧸ Subgroup.center ↥N)) :=
    nonempty_mulEquiv_map_quotient_center N D₀ hD
  have hS' : LieModel S .PSL 4 2 2 := LieModel.of_mulEquiv e.symm hS
  have hC : ∀ y : H ⧸ D₀, (∀ s ∈ S, y * s = s * y) → y = 1 :=
    fun y hy => eq_one_of_commute_image_of_perfect N D₀ hN hD y hy
  have hd2' : (d : H ⧸ D₀) * (d : H ⧸ D₀) = 1 := by
    rw [← QuotientGroup.mk_mul, hd2, QuotientGroup.mk_one]
  obtain ⟨h1, h2⟩ :=
    card_centralizer_ge_and_not_seven_dvd_of_lieModel (Y := H ⧸ D₀) S A hS' hC hAS eA
      t (d : H ⧸ D₀) ht1 ht2 htA hd2' hdt hdA hdout
  exact fun h7 => dvd_card_inf_of_dvd_centralizer_of_not_dvd_quotient D₀ d Nat.prime_seven h7 h2

end CFSG.OddStandard.AltStdSec.SwapPartner
