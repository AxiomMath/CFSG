module

public import CFSG.LieType.ChevTwo.Layered

public section

namespace CFSG.LieType.ChevTwo

open CFSG.Open

variable {W W' : Type}

theorem IsChevTwoLayered.of_surjective [Group W] [Group W'] [Finite W]
    (φ : W →* W') (hφ : Function.Surjective φ) (hker : Group.IsSolvable ↥φ.ker)
    (h : IsChevTwoLayered W) : IsChevTwoLayered W' :=
  (h.quotient φ.ker hker).of_mulEquiv (QuotientGroup.quotientKerEquivOfSurjective φ hφ).symm

theorem IsChevTwoLayered.of_commute_sup [Group W] [Finite W] (K₁ K₂ : Subgroup W)
    (hc : ∀ a ∈ K₁, ∀ b ∈ K₂, Commute a b) (hsup : K₁ ⊔ K₂ = ⊤)
    (h₁ : IsChevTwoLayered ↥K₁) (h₂ : IsChevTwoLayered ↥K₂) : IsChevTwoLayered W := by
  let f : ↥K₁ × ↥K₂ →* W :=
    { toFun := fun p => (p.1 : W) * (p.2 : W)
      map_one' := by simp
      map_mul' := fun p q => by
        have hpq : Commute (q.1 : W) (p.2 : W) := hc q.1 q.1.2 p.2 p.2.2
        simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
        calc ((p.1 : W) * q.1) * (p.2 * q.2)
            = (p.1 : W) * (q.1 * p.2) * q.2 := by group
          _ = (p.1 : W) * (p.2 * q.1) * q.2 := by rw [hpq.eq]
          _ = ((p.1 : W) * p.2) * (q.1 * q.2) := by group }
  have hf : Function.Surjective f := by
    have hle : K₁ ⊔ K₂ ≤ f.range := by
      refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [f]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [f]⟩
    rw [hsup] at hle
    exact MonoidHom.range_eq_top.mp (top_le_iff.mp hle)
  have hker_comm : ∀ p q : f.ker, p * q = q * p := by
    intro p q
    have hp : (p.1.1 : W) * (p.1.2 : W) = 1 := by
      simpa [f] using MonoidHom.mem_ker.mp p.2
    have hq : (q.1.1 : W) * (q.1.2 : W) = 1 := by
      simpa [f] using MonoidHom.mem_ker.mp q.2
    have hpb : (p.1.2 : W) = (p.1.1 : W)⁻¹ := by
      calc (p.1.2 : W) = (p.1.1 : W)⁻¹ * ((p.1.1 : W) * p.1.2) := by group
        _ = (p.1.1 : W)⁻¹ * 1 := by rw [hp]
        _ = (p.1.1 : W)⁻¹ := by rw [mul_one]
    have hqd : (q.1.2 : W) = (q.1.1 : W)⁻¹ := by
      calc (q.1.2 : W) = (q.1.1 : W)⁻¹ * ((q.1.1 : W) * q.1.2) := by group
        _ = (q.1.1 : W)⁻¹ * 1 := by rw [hq]
        _ = (q.1.1 : W)⁻¹ := by rw [mul_one]
    have hcomm_ac : Commute (p.1.1 : W) (q.1.1 : W) := by
      have h1 : Commute (p.1.1 : W) (q.1.2 : W) :=
        hc (p.1.1 : W) p.1.1.2 (q.1.2 : W) q.1.2.2
      rw [hqd] at h1
      simpa using h1.inv_right
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact hcomm_ac.eq
    · apply Subtype.ext
      simp only [Subgroup.coe_mul, Prod.snd_mul]
      rw [hpb, hqd]
      simpa [mul_inv_rev] using (congrArg Inv.inv hcomm_ac.eq).symm
  have hker_solv : Group.IsSolvable ↥f.ker :=
    Group.isSolvable_of_comm hker_comm
  exact IsChevTwoLayered.of_surjective f hf hker_solv (h₁.prod h₂)

theorem IsChevTwoLayered.quotient_of_sup_eq_top [Group W] [Finite W] {L Q : Subgroup W}
    [Q.Normal] (hQ : Group.IsSolvable ↥Q) (hsup : L ⊔ Q = ⊤) (hL : IsChevTwoLayered ↥L) :
    IsChevTwoLayered (W ⧸ Q) := by
  let φ : ↥L →* W ⧸ Q := (QuotientGroup.mk' Q).comp L.subtype
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Q x
    have hw : w ∈ L ⊔ Q := by rw [hsup]; exact Subgroup.mem_top w
    obtain ⟨l, hl, q, hq, hlq⟩ := Subgroup.mem_sup_of_normal_right.mp hw
    refine ⟨⟨l, hl⟩, ?_⟩
    have hq1 : QuotientGroup.mk' Q q = 1 := (QuotientGroup.eq_one_iff q).2 hq
    calc φ ⟨l, hl⟩ = QuotientGroup.mk' Q l * QuotientGroup.mk' Q q := by
          simp [φ, hq1]
      _ = QuotientGroup.mk' Q (l * q) := (map_mul _ _ _).symm
      _ = QuotientGroup.mk' Q w := by rw [hlq]
  let ψ : ↥φ.ker →* ↥Q :=
    { toFun := fun x =>
        ⟨(x.1 : W), (QuotientGroup.eq_one_iff (x.1 : W)).1 (MonoidHom.mem_ker.mp x.2)⟩
      map_one' := Subtype.ext rfl
      map_mul' := fun a b => Subtype.ext rfl }
  have hψ : Function.Injective ψ := by
    intro a b hab
    have h : (a.1 : W) = (b.1 : W) := congrArg (fun z : ↥Q => (z : W)) hab
    exact Subtype.ext (Subtype.ext h)
  haveI : Group.IsSolvable ↥Q := hQ
  have hker_solv : Group.IsSolvable ↥φ.ker :=
    Group.isSolvable_of_isSolvable_injective (f := ψ) hψ
  exact IsChevTwoLayered.of_surjective φ hφ hker_solv hL

end CFSG.LieType.ChevTwo
