module

public import CFSG.LocalAnalysis.RankThreeTheoremC.HasPrimeConstraintBridge
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFPreimage

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.RankThreeCoreUniqueness.Helpers

variable {X Y : Type*} [Group X] [Group Y]

theorem card_comap_of_surjective [Finite X] (f : X →* Y) (hf : Function.Surjective f)
    (L : Subgroup Y) : Nat.card (L.comap f) = Nat.card f.ker * Nat.card L := by
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict (L.comap f))
  have hker : (f.domRestrict (L.comap f)).ker = f.ker.subgroupOf (L.comap f) := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hrange : (f.domRestrict (L.comap f)).range = L := by
    ext φ
    rw [MonoidHom.mem_range]
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hφ
      obtain ⟨y, rfl⟩ := hf φ
      exact ⟨⟨y, hφ⟩, rfl⟩
  have hle : f.ker ≤ L.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.1 hx]
    exact L.one_mem
  rw [hker, hrange, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv] at h
  rw [← h]

theorem primeComplementCore_eq_comap [Finite X] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker)) :
    primeComplementCore (G := X) p = (primeComplementCore (G := Y) p).comap f := by
  have : Finite Y := Finite.of_surjective f hf
  apply le_antisymm
  · have h1 : ((primeComplementCore (G := X) p).map f).Normal :=
      Subgroup.Normal.map inferInstance f hf
    have h2 : (primeComplementCore (G := X) p).map f ≤ primeComplementCore (G := Y) p :=
      normal_coprime_le_primeComplementCore p _ h1
        ((primeComplementCore_coprime p).of_dvd_right
          ((primeComplementCore (G := X) p).card_map_dvd f))
    exact Subgroup.map_le_iff_le_comap.1 h2
  · refine normal_coprime_le_primeComplementCore p _ inferInstance ?_
    rw [card_comap_of_surjective f hf]
    exact hker.mul_right (primeComplementCore_coprime p)

noncomputable def quotientEquivOfCoprimeKer [Finite X] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker)) :
    X ⧸ primeComplementCore (G := X) p ≃* Y ⧸ primeComplementCore (G := Y) p := by
  have hle : primeComplementCore (G := X) p ≤ (primeComplementCore (G := Y) p).comap f :=
    (primeComplementCore_eq_comap f hf hker).le
  refine MulEquiv.ofBijective (QuotientGroup.map _ _ f hle) ⟨?_, ?_⟩
  · rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_map, ← primeComplementCore_eq_comap f hf hker,
      QuotientGroup.map_mk'_self]
  · intro y
    obtain ⟨y', rfl⟩ := QuotientGroup.mk_surjective y
    obtain ⟨x, rfl⟩ := hf y'
    exact ⟨QuotientGroup.mk x, rfl⟩

theorem hasPrimeConstraint_of_surjective_of_coprime_ker [Finite X] {p : ℕ} (f : X →* Y)
    (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    (h : HasPrimeConstraint (G := X) p) : HasPrimeConstraint (G := Y) p := by
  obtain ⟨N, hNn, hNp, hNc⟩ := h
  set e := quotientEquivOfCoprimeKer f hf hker
  refine ⟨N.map e.toMonoidHom, hNn.map e.toMonoidHom e.surjective, hNp.map e.toMonoidHom, ?_⟩
  intro c hc
  have hc' : e.symm c ∈ Subgroup.centralizer (N : Set (X ⧸ primeComplementCore (G := X) p)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    have := Subgroup.mem_centralizer_iff.1 hc (e n) ⟨n, hn, rfl⟩
    apply e.injective
    simpa using this
  have := hNc hc'
  exact ⟨e.symm c, this, by simp⟩

theorem isPConstrained_of_surjective_of_coprime_ker [Finite X] {p : ℕ} [Fact p.Prime]
    (f : X →* Y) (hf : Function.Surjective f) (hker : p.Coprime (Nat.card f.ker))
    (h : CFSG.ABGLocalTools.IsPConstrained p X) : CFSG.ABGLocalTools.IsPConstrained p Y := by
  have : Finite Y := Finite.of_surjective f hf
  rw [CFSG.LocalAnalysis.RankThreeTheoremC.isPConstrained_iff_hasPrimeConstraint] at h ⊢
  exact hasPrimeConstraint_of_surjective_of_coprime_ker f hf hker h

open CFSG.Quasithin CFSG.Open in
theorem isPConstrained_autI_of_coprime {G : Type*} [Group G] [Finite G] {V M : Subgroup G}
    (hV : IsElemAbelian 2 V) (hM : M ≤ Subgroup.normalizer (V : Set G))
    (hC3 : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M))
    (hcon : CFSG.ABGLocalTools.IsPConstrained 3 ↥M) :
    CFSG.ABGLocalTools.IsPConstrained 3 ↥(autI hV M) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥M →* ↥(autI hV M) := (actM hV hM).codRestrict (autI hV M) (fun g => by
    rw [← range_actM hV hM]; exact ⟨g, rfl⟩)
  have hf : Function.Surjective f := by
    intro φ
    have : (φ : MulAut (IntMod V hV)) ∈ (actM hV hM).range := by
      rw [range_actM hV hM]; exact φ.2
    obtain ⟨g, hg⟩ := this
    exact ⟨g, Subtype.ext hg⟩
  have hker : f.ker = (actM hV hM).ker := by
    ext g
    simp only [MonoidHom.mem_ker, f]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hcard : Nat.card f.ker = Nat.card ↥(Subgroup.centralizer (V : Set G) ⊓ M) := by
    rw [hker, ker_actM hV hM]
    have := Nat.card_congr (Subgroup.equivMapOfInjective
      ((Subgroup.centralizer (V : Set G)).subgroupOf M) M.subtype M.subtype_injective).toEquiv
    rwa [Subgroup.subgroupOf_map_subtype] at this
  exact isPConstrained_of_surjective_of_coprime_ker f hf
    (by rw [hcard]; exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hC3) hcon

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
