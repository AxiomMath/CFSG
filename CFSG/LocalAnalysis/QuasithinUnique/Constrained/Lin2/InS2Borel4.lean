module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel3
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InS2Borel2

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ} {t : G}
  {M₀ : Subgroup G} {x₀ : G} {q : ℕ} {W : Subgroup G}

namespace S2Base

variable (B : S2Base T M H S L D n t M₀ x₀ q W)
include B

theorem R₂_le_normalizer_R₁ :
    thompsonJ S ⊓ conjR L t ≤ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) :=
  le_normalizer_of_commute fun a ha b hb => B.comm_elem a ha.2 b hb.2

theorem exists_torus : ∃ D₁ D₂ : Subgroup G,
    BlockTorus L (thompsonJ S ⊓ L) D₁ n ∧ BlockTorus (conjR L t) (thompsonJ S ⊓ conjR L t) D₂ n ∧
      D = D₁ ⊔ D₂ := by
  obtain ⟨F₁, _, _, ⟨A₁⟩⟩ := B.coord₁
  obtain ⟨F₂, _, _, ⟨A₂⟩⟩ := B.coord₂
  have hn : 0 < n := by have := B.hn; omega
  have hR₁2 : IsPGroup 2 ↥(thompsonJ S ⊓ L) := B.R_isPGroup.to_inf_left
  have hR₂2 : IsPGroup 2 ↥(thompsonJ S ⊓ conjR L t) := B.R_isPGroup.to_inf_left
  obtain ⟨T₁, hT₁, hT₁c⟩ := A₁.exists_complement hn hR₁2
  obtain ⟨T₂, hT₂, hT₂c⟩ := A₂.exists_complement hn hR₂2
  have hPF : S ⊓ conjJoin S L ≤ conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G) :=
    le_inf inf_le_right Subgroup.le_normalizer
  have hTT₁ : ∀ a ∈ T₁, ∀ b ∈ T₂, a * b = b * a := fun a ha b hb =>
    B.comm_elem a (hT₁.1 ha).1 b (hT₂.1 hb).1
  have hdecT : ∀ f ∈ conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G),
      ∃ p ∈ S ⊓ conjJoin S L, ∃ tt ∈ T₁ ⊔ T₂, f = p * tt := by
    intro f hf
    obtain ⟨a, ha, b, hb, rfl⟩ := B.N_P_decomp hf
    obtain ⟨r₁, hr₁, t₁, ht₁, hat⟩ := hT₁.2.2 a ha
    obtain ⟨r₂, hr₂, t₂, ht₂, hbt⟩ := hT₂.2.2 b hb
    refine ⟨r₁ * r₂, Subgroup.mul_mem _ (B.R₁_le_P hr₁) (B.R₂_le_P hr₂), t₁ * t₂,
      Subgroup.mul_mem _ (Subgroup.mem_sup_left ht₁) (Subgroup.mem_sup_right ht₂), ?_⟩
    rw [hat, hbt]
    have hc : t₁ * r₂ = r₂ * t₁ := B.comm_elem t₁ (hT₁.1 ht₁).1 r₂ hr₂.2
    calc r₁ * t₁ * (r₂ * t₂) = r₁ * (t₁ * r₂) * t₂ := by group
      _ = r₁ * (r₂ * t₁) * t₂ := by rw [hc]
      _ = r₁ * r₂ * (t₁ * t₂) := by group
  have hbotT : (S ⊓ conjJoin S L) ⊓ (T₁ ⊔ T₂) = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyP, hyT⟩
    have hyP' : y ∈ (thompsonJ S ⊓ L) ⊔ (thompsonJ S ⊓ conjR L t) := B.S_inf_L₀_eq ▸ hyP
    obtain ⟨r₁, hr₁, r₂, hr₂, rfl⟩ := (mem_sup_iff_of_le_normalizer B.R₂_le_normalizer_R₁).1 hyP'
    have hN : T₂ ≤ Subgroup.normalizer (T₁ : Set G) :=
      le_normalizer_of_commute fun a ha b hb => hTT₁ a ha b hb
    obtain ⟨t₁, ht₁, t₂, ht₂, hy⟩ := (mem_sup_iff_of_le_normalizer hN).1 hyT
    have hz : t₁⁻¹ * r₁ = t₂ * r₂⁻¹ := by
      calc t₁⁻¹ * r₁ = t₁⁻¹ * (r₁ * r₂) * r₂⁻¹ := by group
        _ = t₁⁻¹ * (t₁ * t₂) * r₂⁻¹ := by rw [hy]
        _ = t₂ * r₂⁻¹ := by group
    have hzL : t₁⁻¹ * r₁ ∈ L := L.mul_mem (L.inv_mem (hT₁.1 ht₁).1) hr₁.2
    have hzL₂ : t₁⁻¹ * r₁ ∈ conjR L t := by
      rw [hz]; exact (conjR L t).mul_mem (hT₂.1 ht₂).1 ((conjR L t).inv_mem hr₂.2)
    have hz1 : t₁⁻¹ * r₁ = 1 := by
      have : t₁⁻¹ * r₁ ∈ L ⊓ conjR L t := ⟨hzL, hzL₂⟩
      rw [B.L_inf_L₂, Subgroup.mem_bot] at this
      exact this
    have hr₁t₁ : r₁ = t₁ := by
      have := congrArg (fun z => t₁ * z) hz1
      simpa using this
    have hr₂t₂ : t₂ = r₂ := by
      have h2 : t₂ * r₂⁻¹ = 1 := hz.symm.trans hz1
      have := congrArg (fun z => z * r₂) h2
      simpa using this
    have h1 : r₁ ∈ (thompsonJ S ⊓ L) ⊓ T₁ := ⟨hr₁, hr₁t₁ ▸ ht₁⟩
    have h2 : r₂ ∈ (thompsonJ S ⊓ conjR L t) ⊓ T₂ := ⟨hr₂, hr₂t₂ ▸ ht₂⟩
    rw [hT₁.2.1, Subgroup.mem_bot] at h1
    rw [hT₂.2.1, Subgroup.mem_bot] at h2
    rw [h1, h2, mul_one]
    exact Subgroup.one_mem _
  have hcompT : IsComplementIn (S ⊓ conjJoin S L) (conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) (T₁ ⊔ T₂) :=
    ⟨sup_le (hT₁.1.trans B.B₁_le_F) (hT₂.1.trans B.B₂_le_F), hbotT, hdecT⟩
  have hcompD : IsComplementIn (S ⊓ conjJoin S L) (conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) D :=
    ⟨le_inf B.D_le_L₀ B.D_le_normalizer_P, by rw [inf_comm]; exact B.inf_M_decomp.1,
      fun f hf => B.inf_M_decomp.2.2 f (by rw [B.inf_M_eq]; exact hf)⟩
  have hrel : (S ⊓ conjJoin S L).relIndex (conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) = (2 ^ n - 1) ^ 2 := by
    have h := Subgroup.relIndex_mul_card (H := S ⊓ conjJoin S L) (K := conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G))
    rw [inf_eq_left.mpr hPF, B.card_F] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (by rw [h, mul_comm])
  have hodd : ¬ 2 ∣ (S ⊓ conjJoin S L).relIndex (conjJoin S L ⊓
      Subgroup.normalizer ((S ⊓ conjJoin S L : Subgroup G) : Set G)) := by
    rw [hrel]
    intro h2
    have h3 := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h2
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hx : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    rw [pow_succ] at h3
    omega
  obtain ⟨r, hr, hDeq⟩ := exists_conj_of_complements hPF inf_le_right B.P_isPGroup hodd hcompT.1
    hcompD.1 hcompT.2.1 hcompD.2.1 hcompT.2.2 hcompD.2.2
  have hrB₁ : r ∈ Subgroup.normalizer ((L ⊓ Subgroup.normalizer
      ((thompsonJ S ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    have hP : S ⊓ conjJoin S L ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer
        ((thompsonJ S ⊓ L : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      rw [B.S_inf_L₀_eq]
      refine sup_le (fun r₁ hr₁ => Subgroup.le_normalizer ⟨hr₁.2, Subgroup.le_normalizer hr₁⟩) ?_
      exact le_normalizer_of_commute fun a ha b hb => B.comm_elem a ha.1 b hb.2
    exact hP hr
  have hrB₂ : r ∈ Subgroup.normalizer ((conjR L t ⊓ Subgroup.normalizer
      ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
    have hP : S ⊓ conjJoin S L ≤ Subgroup.normalizer ((conjR L t ⊓ Subgroup.normalizer
        ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) : Subgroup G) : Set G) := by
      rw [B.S_inf_L₀_eq]
      refine sup_le ?_ (fun r₂ hr₂ => Subgroup.le_normalizer ⟨hr₂.2, Subgroup.le_normalizer hr₂⟩)
      exact le_normalizer_of_commute fun a ha b hb => (B.comm_elem b hb.2 a ha.1).symm
    exact hP hr
  have hD₁ : conjR T₁ r ≤ L ⊓ Subgroup.normalizer ((thompsonJ S ⊓ L : Subgroup G) : Set G) := by
    have := conjR_mono hT₁.1 r
    rwa [conjR_eq_of_mem_normalizer hrB₁] at this
  have hD₂ : conjR T₂ r ≤ conjR L t ⊓
      Subgroup.normalizer ((thompsonJ S ⊓ conjR L t : Subgroup G) : Set G) := by
    have := conjR_mono hT₂.1 r
    rwa [conjR_eq_of_mem_normalizer hrB₂] at this
  refine ⟨conjR T₁ r, conjR T₂ r, A₁.blockTorus hn hR₁2 hD₁ (by rw [card_conjR]; exact hT₁c),
    A₂.blockTorus hn hR₂2 hD₂ (by rw [card_conjR]; exact hT₂c), ?_⟩
  rw [hDeq, conjR_sup]

end S2Base

end CFSG.QuasithinUnique.Lin2
