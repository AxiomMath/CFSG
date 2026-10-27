module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhatDefs
public import CFSG.LieType.Ree.LargeReeA1Pair
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.Quasithin.H13.NQBlockPRankProduct

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped Pointwise

theorem commute_pinnedX_of_pi_single {τ : Tag} {K : Type} [Field K] {a b : Fin τ.rank} (hab : a ≠ b)
    (hcheck : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → (∀ k, k ≠ a → k ≠ b → γ k = 0) →
      γ a = 0 ∨ γ b = 0)
    {s t : Fin τ.rank → ℤ} (hs : s = Pi.single a 1 ∨ s = -Pi.single a 1)
    (ht : t = Pi.single b 1 ∨ t = -Pi.single b 1) (c d : K) :
    Commute (pinnedX τ K s c) (pinnedX τ K t d) := by
  have hsr : IsRoot τ s := by
    rcases hs with rfl | rfl
    exacts [isRoot_single τ a, IsRoot.neg (isRoot_single τ a)]
  have htr : IsRoot τ t := by
    rcases ht with rfl | rfl
    exacts [isRoot_single τ b, IsRoot.neg (isRoot_single τ b)]
  have hsa : s a ≠ 0 := by rcases hs with rfl | rfl <;> simp
  have hta : t a = 0 := by
    rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hab]
  refine CFSG.LieType.Ree.commute_pinnedX_of_forall_not_isRoot (R := K) hsr htr ?_ ?_ ?_ c d
  · intro h
    apply hsa
    rw [h, hta]
  · intro h
    apply hsa
    rw [h, Pi.neg_apply, hta, neg_zero]
  · intro m n hm hn hroot
    have hk : ∀ k, k ≠ a → k ≠ b → (m • s + n • t) k = 0 := by
      intro k hka hkb
      rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hka, hkb]
    rcases hcheck _ hroot hk with h | h
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [hab] at h <;> omega
    · rcases hs with rfl | rfl <;> rcases ht with rfl | rfl <;> simp [Ne.symm hab] at h <;> omega

theorem commute_subsystemGroup {τ : Tag} {K : Type} [Field K] {A B : Set (Fin τ.rank)}
    (h : ∀ a ∈ A, ∀ b ∈ B, a ≠ b ∧ ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ →
      (∀ k, k ≠ a → k ≠ b → γ k = 0) → γ a = 0 ∨ γ b = 0) :
    ∀ x ∈ subsystemGroup τ K A, ∀ y ∈ subsystemGroup τ K B, Commute x y := by
  have hgen : ∀ x ∈ {g | ∃ i ∈ A, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c},
      ∀ y ∈ {g | ∃ i ∈ B, ∃ c : K, g = xUnit τ K i c ∨ g = yUnit τ K i c}, Commute x y := by
    rintro _ ⟨a, ha, c, rfl | rfl⟩ _ ⟨b, hb, d, rfl | rfl⟩
    · rw [← pinnedX_single, ← pinnedX_single]
      exact commute_pinnedX_of_pi_single (h a ha b hb).1 (h a ha b hb).2 (Or.inl rfl) (Or.inl rfl) c d
    · rw [← pinnedX_single, ← pinnedX_neg_single]
      exact commute_pinnedX_of_pi_single (h a ha b hb).1 (h a ha b hb).2 (Or.inl rfl) (Or.inr rfl) c d
    · rw [← pinnedX_neg_single, ← pinnedX_single]
      exact commute_pinnedX_of_pi_single (h a ha b hb).1 (h a ha b hb).2 (Or.inr rfl) (Or.inl rfl) c d
    · rw [← pinnedX_neg_single, ← pinnedX_neg_single]
      exact commute_pinnedX_of_pi_single (h a ha b hb).1 (h a ha b hb).2 (Or.inr rfl) (Or.inr rfl) c d
  intro x hx y hy
  have hle : subsystemGroup τ K B ≤ Subgroup.centralizer (subsystemGroup τ K A : Set _) := by
    refine (Subgroup.closure_le _).2 fun y hy => ?_
    have hle' : subsystemGroup τ K A ≤ Subgroup.centralizer ({y} : Set (ModGL τ K)) :=
      (Subgroup.closure_le _).2 fun x hx =>
        Subgroup.mem_centralizer_singleton_iff.2 (hgen x hx y hy).eq
    exact Subgroup.mem_centralizer_iff.2 fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.1 (hle' hx)
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

section Product

variable {G : Type*} [Group G] [Finite G]

theorem card_comap_of_le_range {X Y : Type*} [Group X] [Group Y] [Finite X] (f : X →* Y)
    {H : Subgroup Y} (hH : H ≤ f.range) :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  let f' : ↥(H.comap f) →* ↥H := (f.comp (H.comap f).subtype).codRestrict H fun x => x.2
  have hsurj : Function.Surjective f' := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hH hy
    exact ⟨⟨x, hy⟩, rfl⟩
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f'.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f' hsurj).toEquiv] at h1
  rw [h1, mul_comm]
  congr 1
  refine Nat.card_congr
    { toFun := fun x => ⟨((x : ↥(H.comap f)) : X), ?_⟩
      invFun := fun y => ⟨⟨y, ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have h2 : f' x = 1 := x.2
    exact congrArg Subtype.val h2
  · rw [Subgroup.mem_comap, y.2]
    exact H.one_mem
  · apply Subtype.ext
    exact y.2

theorem card_ker_noncommCoprod_dvd {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) :
    Nat.card (A.subtype.noncommCoprod B.subtype (fun a b => hcomm a a.2 b b.2)).ker ∣
      Nat.card ↥(A ⊓ B) := by
  let Φ : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype (fun a b => hcomm a a.2 b b.2)
  have hΦapply : ∀ x : ↥A × ↥B, Φ x = (x.1 : G) * (x.2 : G) := fun _ => rfl
  have key : ∀ x : Φ.ker, ((x : ↥A × ↥B).1 : G) * ((x : ↥A × ↥B).2 : G) = 1 := by
    intro x
    have hx : Φ (x : ↥A × ↥B) = 1 := MonoidHom.mem_ker.1 x.2
    rwa [hΦapply] at hx
  let ψ : Φ.ker →* ↥(A ⊓ B) :=
    { toFun := fun x =>
        (⟨((x : ↥A × ↥B).1 : G),
          ⟨((x : ↥A × ↥B).1).2, by
            have hx := key x
            have hx2 : ((x : ↥A × ↥B).2 : G) = (((x : ↥A × ↥B).1 : G))⁻¹ :=
              eq_inv_of_mul_eq_one_right hx
            rw [show ((x : ↥A × ↥B).1 : G) = (((x : ↥A × ↥B).2 : G))⁻¹ from by
              rw [hx2, inv_inv]]
            exact B.inv_mem (x : ↥A × ↥B).2.2⟩⟩ : ↥(A ⊓ B))
      map_one' := Subtype.ext rfl
      map_mul' := fun x y => Subtype.ext rfl }
  have hinj : Function.Injective ψ := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have h1 : ((x : ↥A × ↥B).1 : G) = ((y : ↥A × ↥B).1 : G) :=
      congrArg (fun z : ↥(A ⊓ B) => (z : G)) hxy
    have hx2 : ((x : ↥A × ↥B).2 : G) = (((x : ↥A × ↥B).1 : G))⁻¹ :=
      eq_inv_of_mul_eq_one_right (key ⟨x, hx⟩)
    have hy2 : ((y : ↥A × ↥B).2 : G) = (((y : ↥A × ↥B).1 : G))⁻¹ :=
      eq_inv_of_mul_eq_one_right (key ⟨y, hy⟩)
    refine Subtype.ext (Prod.ext (Subtype.ext h1) (Subtype.ext ?_))
    rw [hx2, hy2, h1]
  have hcard : Nat.card Φ.ker = Nat.card ψ.range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  exact Subgroup.card_subgroup_dvd_card ψ.range

theorem not_dvd_card_ker_noncommCoprod {p : ℕ} {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hinf : ¬ p ∣ Nat.card ↥(A ⊓ B)) :
    ¬ p ∣ Nat.card (A.subtype.noncommCoprod B.subtype (fun a b => hcomm a a.2 b b.2)).ker :=
  fun hd => hinf (hd.trans (card_ker_noncommCoprod_dvd hcomm))

theorem card_le_pow_add_of_le_sup_of_not_dvd_inf {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ B, Commute x y) (hinf : ¬ p ∣ Nat.card ↥(A ⊓ B)) {k₁ k₂ : ℕ}
    (hA : ∀ F : Subgroup A, IsElemAbelian p F → Nat.card F ≤ p ^ k₁)
    (hB : ∀ F : Subgroup B, IsElemAbelian p F → Nat.card F ≤ p ^ k₂)
    {E : Subgroup G} (hE : E ≤ A ⊔ B) (hEel : IsElemAbelian p E) :
    Nat.card E ≤ p ^ (k₁ + k₂) := by
  haveI : Fact p.Prime := ⟨hp⟩
  let Φ : ↥A × ↥B →* G := A.subtype.noncommCoprod B.subtype (fun x y => hcomm x x.2 y y.2)
  have hΦapply : ∀ x : ↥A × ↥B, Φ x = (x.1 : G) * (x.2 : G) := fun _ => rfl
  have hΦrange : Φ.range = A ⊔ B :=
    (MonoidHom.noncommCoprod_range _ _ _).trans (by
      rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have hpker : ¬ p ∣ Nat.card Φ.ker := not_dvd_card_ker_noncommCoprod hcomm hinf
  let Et : Subgroup (↥A × ↥B) := E.comap Φ
  have hEtmap : (Φ.comp Et.subtype).range = E := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq_self]
    exact hΦrange ▸ hE
  have hkerdvd : Nat.card (Φ.comp Et.subtype).ker ∣ Nat.card Φ.ker := by
    let f : (Φ.comp Et.subtype).ker →* Φ.ker :=
      { toFun := fun x =>
          ⟨((x : Et) : ↥A × ↥B), by
            show Φ ((x : Et) : ↥A × ↥B) = 1
            exact MonoidHom.mem_ker.1 x.2⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    have hinj : Function.Injective f := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : Φ.ker => ((z : Φ.ker) : ↥A × ↥B)) h))
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).dvd.trans
      (Subgroup.card_subgroup_dvd_card f.range)
  have hpker' : ¬ p ∣ Nat.card (Φ.comp Et.subtype).ker :=
    fun hd => hpker (hd.trans hkerdvd)
  have hEtrank : CFSG.Open.pRank p (⊤ : Subgroup Et) = CFSG.Open.pRank p (⊤ : Subgroup E) := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup (Et ⧸ (Φ.comp Et.subtype).ker)) =
        CFSG.Open.pRank p (⊤ : Subgroup Et) :=
      CFSG.SectionRank.pRank_quotient_eq (Φ.comp Et.subtype).ker hpker'
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup (Et ⧸ (Φ.comp Et.subtype).ker)) =
        CFSG.Open.pRank p (⊤ : Subgroup E) := by
      refine CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt ?_
      exact (QuotientGroup.quotientKerEquivRange (Φ.comp Et.subtype)).trans
        (MulEquiv.subgroupCongr hEtmap)
    rw [← h1, h2]
  have hAB : CFSG.Open.pRank p (⊤ : Subgroup (↥A × ↥B)) ≤ k₁ + k₂ := by
    have h1 : CFSG.Open.pRank p (⊤ : Subgroup A) ≤ k₁ :=
      CFSG.SectionRank.pRank_le hp.one_lt fun F _ hF => hA F hF
    have h2 : CFSG.Open.pRank p (⊤ : Subgroup B) ≤ k₂ :=
      CFSG.SectionRank.pRank_le hp.one_lt fun F _ hF => hB F hF
    exact (CFSG.Quasithin.H13.NQBlock.pRank_prod_le (S := ↥A) (T := ↥B) hp).trans
      (by omega)
  have hEtr : CFSG.Open.pRank p (⊤ : Subgroup Et) ≤ k₁ + k₂ := by
    refine (CFSG.SectionRank.pRank_le_map hp.one_lt Et.subtype Subtype.val_injective ⊤).trans ?_
    exact (CFSG.SectionRank.pRank_mono hp.one_lt le_top).trans hAB
  have hEcard : Nat.card E = p ^ CFSG.Open.pRank p (⊤ : Subgroup E) := by
    obtain ⟨k, hk⟩ := (hEel.isPGroup : IsPGroup p E).exists_card_eq
    have hk' : k = CFSG.Open.pRank p (⊤ : Subgroup E) := by
      rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup E]
      refine le_antisymm (CFSG.SectionRank.le_pRank hp.one_lt (le_refl E) hEel hk) ?_
      refine CFSG.SectionRank.pRank_le hp.one_lt fun F hF hFel => ?_
      calc Nat.card F ≤ Nat.card E := Subgroup.card_le_of_le hF
        _ = p ^ k := hk
    rw [hk, hk']
  rw [hEcard, ← hEtrank]
  exact Nat.pow_le_pow_right hp.pos hEtr

end Product

end CFSG.LocalAnalysis.GLTheoremA
