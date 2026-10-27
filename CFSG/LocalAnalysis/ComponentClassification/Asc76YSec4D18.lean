module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4ALemma49
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YFischer
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D10

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem DBar.nonempty (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hΩne : Ω.Nonempty) : (DBar Ω (sec4W Ω S)).Nonempty := by
  obtain ⟨K₁, hK₁⟩ := hΩne
  obtain ⟨L, hLΩ, T, hT, hTW⟩ := exists_mem_omegaD hΩ hS hK₁
  have hTD : T ∈ DSet Ω (sec4W Ω S) := ⟨⟨L, hLΩ, hT⟩, hTW⟩
  obtain ⟨d, hd⟩ := IsBarOf.exists_of_mem hΩ hTD
  exact ⟨d, IsBarOf.mem_dBar hTD hd⟩

theorem perm_three_eq_of_commute (σ τ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (h3 : τ ≠ 1) (h4 : τ * τ = 1) (h5 : σ * τ = τ * σ) : σ = τ := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3), σ = 1 ∨ σ * σ ≠ 1 ∨ τ = 1 ∨ τ * τ ≠ 1 ∨
      σ * τ ≠ τ * σ ∨ σ = τ := by decide
  rcases key σ τ with h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h2 h
  · exact absurd h h3
  · exact absurd h4 h
  · exact absurd h5 h
  · exact h

theorem perm_three_conj_ne (σ τ : Equiv.Perm (Fin 3)) (h1 : σ ≠ 1) (h2 : σ * σ = 1)
    (h3 : τ ≠ 1) (h4 : τ * τ = 1) (h5 : σ ≠ τ) : τ * σ * τ ≠ σ := by
  have key : ∀ σ τ : Equiv.Perm (Fin 3), σ = 1 ∨ σ * σ ≠ 1 ∨ τ = 1 ∨ τ * τ ≠ 1 ∨
      σ = τ ∨ τ * σ * τ ≠ σ := by decide
  rcases key σ τ with h | h | h | h | h | h
  · exact absurd h h1
  · exact absurd h2 h
  · exact absurd h h3
  · exact absurd h4 h
  · exact absurd h h5
  · exact h

@[expose] def commGraphIsoSubtype {X : Type} [Group X] (M : Subgroup X) {K : Set X}
    (hKM : K ⊆ M) : CFSG.Fischer.commGraph (Subtype.val ⁻¹' K : Set M) ≃g
      CFSG.Fischer.commGraph K where
  toFun a := ⟨((a : M) : X), a.2⟩
  invFun c := ⟨⟨c, hKM c.2⟩, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' {a b} := by
    change (_ ≠ _ ∧ ((a : M) : X) * ((b : M) : X) = ((b : M) : X) * ((a : M) : X)) ↔ _
    simp only [CFSG.Fischer.commGraph_adj, ne_eq, Subtype.ext_iff]
    rfl

theorem DBar.exists_hom_perm_three (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hΩne : Ω.Nonempty) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) :
    ∃ φ : ↥(MBar Ω (sec4W Ω S)) →* Equiv.Perm (Fin 3), Function.Surjective φ ∧
      φ.ker = CFSG.pCore 2 ↥(MBar Ω (sec4W Ω S)) ∧
      (∀ d : ↥(MBar Ω (sec4W Ω S)), (d : NBar (sec4W Ω S)) ∈ DBar Ω (sec4W Ω S) →
        φ d ≠ 1 ∧ φ d * φ d = 1) ∧
      (∀ d e : ↥(MBar Ω (sec4W Ω S)), (d : NBar (sec4W Ω S)) ∈ DBar Ω (sec4W Ω S) →
        (e : NBar (sec4W Ω S)) ∈ DBar Ω (sec4W Ω S) → (d * e = e * d ↔ φ d = φ e)) ∧
      (∀ d e : ↥(MBar Ω (sec4W Ω S)), (d : NBar (sec4W Ω S)) ∈ DBar Ω (sec4W Ω S) →
        (e : NBar (sec4W Ω S)) ∈ DBar Ω (sec4W Ω S) → IsConj d e) := by
  set W := sec4W Ω S with hWdef
  set X := ↥(MBar Ω W) with hXdef
  set D : Set X := Subtype.val ⁻¹' DBar Ω W with hDdef
  have hDM : DBar Ω W ⊆ (MBar Ω W : Set (NBar W)) := subset_closure
  have hne : D.Nonempty := by
    obtain ⟨d, hd⟩ := DBar.nonempty H.hΩ hS hΩne
    exact ⟨⟨d, hDM hd⟩, hd⟩
  have hD2 : ∀ d ∈ D, orderOf d = 2 := by
    intro d hd
    rw [← Subgroup.orderOf_coe]
    exact DBar.orderOf_eq_two H.hΩ hS hd
  have hDn : ∀ d ∈ D, ∀ x : X, x * d * x⁻¹ ∈ D := by
    intro d hd x
    show ((x * d * x⁻¹ : X) : NBar W) ∈ DBar Ω W
    exact DBar.conj_mem H.hΩ hd (x : NBar W)
  have hD3 : ∀ d ∈ D, ∀ e ∈ D, orderOf (d * e) ≤ 3 := by
    intro d hd e he
    rw [← Subgroup.orderOf_coe, coe_mul]
    exact DBar.orderOf_mul_le_three H.h22 H.hΩ H.hnil hS hd he
  have hgen : closure D = ⊤ := Subgroup.closure_closure_coe_preimage
  have hdis' : ¬ (CFSG.Fischer.commGraph D).Connected := by
    rw [(commGraphIsoSubtype (MBar Ω W) hDM).connected_iff]
    exact hdis
  obtain ⟨hconj, Y, hYn, ⟨e⟩, hYO⟩ := fischerDisconnected X D hne hD2 hDn hD3 hgen hdis'
  set φ : X →* Equiv.Perm (Fin 3) := e.toMonoidHom.comp (QuotientGroup.mk' Y) with hφdef
  have hφsurj : Function.Surjective φ :=
    e.surjective.comp (QuotientGroup.mk'_surjective Y)
  have hker : φ.ker = Y := by
    ext x
    rw [MonoidHom.mem_ker, hφdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hsq : ∀ d ∈ D, d * d = 1 := fun d hd => by
    rw [← pow_two, ← hD2 d hd, pow_orderOf_eq_one]
  have hφ1 : ∀ d ∈ D, φ d ≠ 1 := by
    intro d hd h1
    have hall : ∀ e ∈ D, φ e = 1 := by
      intro e he
      obtain ⟨c, hc⟩ := (isConj_iff).mp (hconj d hd e he)
      rw [← hc, map_mul, map_mul, h1, mul_one, ← map_mul, mul_inv_cancel, map_one]
    have htop : (⊤ : Subgroup X) ≤ φ.ker := by
      rw [← hgen, closure_le]
      intro e he
      exact (MonoidHom.mem_ker).mpr (hall e he)
    obtain ⟨x, hx⟩ := hφsurj (Equiv.swap 0 1)
    have := (MonoidHom.mem_ker).mp (htop (mem_top x))
    rw [hx] at this
    exact absurd this (by decide)
  have hcomm_eq : ∀ d ∈ D, ∀ e ∈ D, d * e = e * d → φ d = φ e := by
    intro d hd e he hde
    apply perm_three_eq_of_commute _ _ (hφ1 d hd) (by rw [← map_mul, hsq d hd, map_one])
      (hφ1 e he) (by rw [← map_mul, hsq e he, map_one])
    rw [← map_mul, hde, map_mul]
  have hdiff : ∀ d ∈ D, ∃ f ∈ D, φ f ≠ φ d := by
    intro d hd
    by_contra hcon
    push Not at hcon
    have hle : (⊤ : Subgroup X) ≤ (zpowers d) ⊔ φ.ker := by
      rw [← hgen, closure_le]
      intro f hf
      have h1 : d⁻¹ * f ∈ φ.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hcon f hf, inv_mul_cancel]
      rw [← mul_inv_cancel_left d f]
      exact mul_mem (mem_sup_left (mem_zpowers d)) (mem_sup_right h1)
    have h2 : ∀ x : X, φ x = 1 ∨ φ x = φ d := by
      intro x
      have hx := hle (mem_top x)
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (by rw [normalizer_eq_top_iff.mpr (MonoidHom.normal_ker φ)]; exact le_top)] at hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      rw [map_mul, (MonoidHom.mem_ker).mp hb, mul_one, map_zpow]
      have hd2 : φ d * φ d = 1 := by rw [← map_mul, hsq d hd, map_one]
      have hdo : orderOf (φ d) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd2)
      rcases Int.emod_two_eq_zero_or_one k with hk | hk
      · left
        rw [← zpow_mod_orderOf, show k % (orderOf (φ d) : ℤ) = 0 by
          obtain ⟨c, hc⟩ := Int.dvd_of_emod_eq_zero hk
          rw [hc]
          exact Int.emod_eq_zero_of_dvd (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr hdo)
            c)]
        rw [zpow_zero]
      · right
        obtain ⟨c, hc⟩ : ∃ c, k = 2 * c + 1 := ⟨k / 2, by omega⟩
        rw [hc, zpow_add, zpow_mul, zpow_one, show (φ d) ^ (2 : ℤ) = 1 by
          rw [zpow_two, hd2], one_zpow, one_mul]
    obtain ⟨x, hx⟩ := hφsurj (Equiv.swap 1 2)
    obtain ⟨y, hy⟩ := hφsurj (Equiv.swap 0 1)
    rcases h2 x with h | h <;> rcases h2 y with h' | h'
    · rw [hx] at h; exact absurd h (by decide)
    · rw [hx] at h; exact absurd h (by decide)
    · rw [hy] at h'; exact absurd h' (by decide)
    · rw [hx] at h; rw [hy] at h'; rw [← h] at h'; exact absurd h' (by decide)
  have heq_comm : ∀ d ∈ D, ∀ e ∈ D, φ d = φ e → d * e = e * d := by
    intro d hd e he hde
    by_contra hne
    obtain ⟨f, hf, hfd⟩ := hdiff d hd
    have hdf : (d : NBar W) * f ≠ f * d := fun h =>
      hfd (hcomm_eq d hd f hf (Subtype.ext h)).symm
    have h49 := lemma49 G Ω H S hS (e : NBar W) (d : NBar W) (f : NBar W) he hd hf hdf
    rcases h49 with h | h | h
    · apply hfd
      rw [hde]
      exact (hcomm_eq e he f hf (Subtype.ext h)).symm
    · exact hne (Subtype.ext h.symm)
    · have hfinv : f⁻¹ = f := inv_eq_of_mul_eq_one_right (hsq f hf)
      have hfdf : f * d * f ∈ D := by
        have := hDn d hd f
        rwa [hfinv] at this
      have h1 : φ e = φ (f * d * f) := hcomm_eq e he _ hfdf (Subtype.ext h)
      rw [map_mul, map_mul, ← hde] at h1
      exact perm_three_conj_ne (φ d) (φ f) (hφ1 d hd) (by rw [← map_mul, hsq d hd, map_one])
        (hφ1 f hf) (by rw [← map_mul, hsq f hf, map_one]) (fun h' => hfd h'.symm) h1.symm
  refine ⟨φ, hφsurj, ?_, fun d hd => ⟨hφ1 d hd, by rw [← map_mul, hsq d hd, map_one]⟩,
    fun d e hd he => ⟨hcomm_eq d hd e he, heq_comm d hd e he⟩, fun d e hd he => hconj d hd e he⟩
  rw [hker]
  obtain ⟨d, hd⟩ := hne
  exact hYO d hd fun e he hde => heq_comm d hd e he (by
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hde
    exact hde)

theorem DBar.commute_trans (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hΩne : Ω.Nonempty) (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {d e f : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) (he : e ∈ DBar Ω (sec4W Ω S))
    (hf : f ∈ DBar Ω (sec4W Ω S)) (hde : d * e = e * d) (hef : e * f = f * e) :
    d * f = f * d := by
  obtain ⟨φ, -, -, -, hcomm, -⟩ := DBar.exists_hom_perm_three H hS hΩne hdis
  have hDM : DBar Ω (sec4W Ω S) ⊆ (MBar Ω (sec4W Ω S) : Set _) := subset_closure
  have h1 := (hcomm ⟨d, hDM hd⟩ ⟨e, hDM he⟩ hd he).mp (Subtype.ext hde)
  have h2 := (hcomm ⟨e, hDM he⟩ ⟨f, hDM hf⟩ he hf).mp (Subtype.ext hef)
  have h3 := (hcomm ⟨d, hDM hd⟩ ⟨f, hDM hf⟩ hd hf).mpr (h1.trans h2)
  exact congrArg Subtype.val h3

end CFSG.ComponentClassification.Asc76.Sec4
