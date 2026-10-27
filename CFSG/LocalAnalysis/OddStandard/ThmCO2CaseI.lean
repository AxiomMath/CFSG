module

public import CFSG.LocalAnalysis.OddStandard.ThmCO2Defs
public import CFSG.LocalAnalysis.OddStandard.ThmCO2Pre
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Grp4cIAut

public section

namespace CFSG.OddStandard.ThmC.O2

open CFSG Subgroup CFSG.GH74.GLS.Bg.TwoGroups CFSG.OddStandard.ThmC

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCore_eq_sylow_of_normal (S : Sylow 2 G) (hSn : (S : Subgroup G).Normal) :
    pCore 2 G = (S : Subgroup G) :=
  le_antisymm ((pCore_isPGroup (p := 2) (G := G)).le_sylow_of_normal S)
    (le_sSup ⟨hSn, S.isPGroup'⟩)

theorem centralizer_le_of_normal (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (td : TData (S : Subgroup G)) (hSn : (S : Subgroup G).Normal) :
    centralizer ((S : Subgroup G) : Set G) ≤ (S : Subgroup G) := by
  have : (centralizer ((S : Subgroup G) : Set G)).Normal := Subgroup.normal_centralizer
  have hZ : td.Z = (S : Subgroup G) ⊓ centralizer ((S : Subgroup G) : Set G) := by
    ext g
    rw [td.mem_Z, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
    constructor
    · rintro ⟨hg, hc⟩
      exact ⟨hg, fun s hs => (hc s hs).symm⟩
    · rintro ⟨hg, hc⟩
      exact ⟨hg, fun s hs => (hc s hs).symm⟩
  have hcent : ∀ x ∈ centralizer ((S : Subgroup G) : Set G), ∀ p ∈ td.Z, x * p = p * x :=
    fun x hx p hp => (Subgroup.mem_centralizer_iff.1 hx p ((td.mem_Z p).1 hp).1).symm
  have hPN : td.Z ≤ centralizer ((S : Subgroup G) : Set G) := by
    intro z hz
    rw [hZ] at hz
    exact (Subgroup.mem_inf.1 hz).2
  have hP : IsPGroup 2 td.Z := IsPGroup.of_card (n := 2) (td.card_Z.trans (by norm_num))
  have hidx : ¬ 2 ∣ td.Z.relIndex (centralizer ((S : Subgroup G) : Set G)) := by
    rw [hZ]
    exact sylow_inf_normal_relIndex_odd S (centralizer ((S : Subgroup G) : Set G))
  have heq := eq_of_central_sylow hO (centralizer ((S : Subgroup G) : Set G)) td.Z hPN hP hidx hcent
  intro x hx
  rw [heq] at hx
  exact ((td.mem_Z x).1 hx).1

theorem dvd_ordCompl_of_not_two_dvd {m n : ℕ} (hm : ¬ 2 ∣ m) (hmn : m ∣ n) :
    m ∣ n / 2 ^ n.factorization 2 := by
  have hcop : Nat.Coprime m (2 ^ n.factorization 2) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 hm).symm
  have hn : 2 ^ n.factorization 2 * (n / 2 ^ n.factorization 2) = n :=
    Nat.ordProj_mul_ordCompl_eq_self n 2
  rw [← hn] at hmn
  exact hcop.dvd_of_dvd_mul_left hmn

theorem index_dvd_nine_of_normal (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G)
    (e : (S : Subgroup G) ≃* SylSL3_4) (td : TData (S : Subgroup G))
    (hSn : (S : Subgroup G).Normal) : (S : Subgroup G).index ∣ 9 := by
  have hC := centralizer_le_of_normal hO S td hSn
  obtain ⟨ψ, hψ⟩ : ∃ ψ : G →* MulAut (S : Subgroup G),
      ∀ (g : G) (h : (S : Subgroup G)), ((ψ g h : (S : Subgroup G)) : G) = g * h * g⁻¹ :=
    ⟨MulAut.conjNormal, fun g h => MulAut.conjNormal_apply g h⟩
  have hker : ψ.ker ≤ (S : Subgroup G) := by
    intro g hg
    apply hC
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h1 : g * h * g⁻¹ = h := by
      have := hψ g ⟨h, hh⟩
      rw [MonoidHom.mem_ker.1 hg] at this
      exact this.symm
    calc h * g = g * h * g⁻¹ * g := by rw [h1]
      _ = g * h := by group
  have hdvd : (S : Subgroup G).index ∣ Nat.card (MulAut (S : Subgroup G)) := by
    have h1 : (S : Subgroup G).index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hker
    rw [Subgroup.index_ker] at h1
    exact h1.trans (Subgroup.card_subgroup_dvd_card _)
  exact (dvd_ordCompl_of_not_two_dvd S.not_dvd_index hdvd).trans
    (CFSG.GH74.GLS.Stage2.Signalizer.Odd87.aut34Odd _ (Nonempty.intro e))

theorem elemAb16_eq {S : Subgroup G} (td : TData S) (B : Subgroup G) (hBS : B ≤ S)
    (hsq : ∀ b ∈ B, b * b = 1) (hcomm : ∀ b ∈ B, ∀ c ∈ B, b * c = c * b)
    (hcard : Nat.card B = 16) : B = td.A ∨ B = td.B := by
  rcases td.elemAb_le B hBS hsq hcomm with h | h
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge h (td.card_A.trans hcard.symm).le)
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge h (td.card_B.trans hcard.symm).le)

theorem conj_map_A_eq {S : Subgroup G} (hSn : S.Normal) (td : TData S) (g : G) :
    td.A.map (MulAut.conj g).toMonoidHom = td.A ∨
      td.A.map (MulAut.conj g).toMonoidHom = td.B := by
  refine elemAb16_eq td _ ?_ ?_ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact hSn.conj_mem a (td.A_le_S ha) g
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, td.A_sq a ha, map_one]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, td.A_abel a ha b hb]
  · rw [Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
      (fun x y h => (MulAut.conj g).injective h), td.card_A]

omit [Finite G] in
theorem le_normalizer_A {S : Subgroup G} (td : TData S) : S ≤ normalizer (td.A : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => td.A_norm s hs a ha, fun h => ?_⟩
  have h1 := td.A_norm s⁻¹ (S.inv_mem hs) _ h
  have h2 : s⁻¹ * (s * a * s⁻¹) * s⁻¹⁻¹ = a := by group
  rwa [h2] at h1

theorem A_normal_of_normal (S : Sylow 2 G) (td : TData (S : Subgroup G))
    (hSn : (S : Subgroup G).Normal) : td.A.Normal := by
  have h := normalizer_of_odd_two ⊤ (S : Subgroup G) td.A td.B le_top
    (by rw [Subgroup.relIndex_top_right]; exact S.not_dvd_index) (le_normalizer_A td)
    (fun h _ => conj_map_A_eq hSn td h)
  rw [← Subgroup.normalizer_eq_top_iff]
  exact top_le_iff.1 h

theorem caseI (hO : pPrimeCore 2 G = ⊥) (S : Sylow 2 G) (e : (S : Subgroup G) ≃* SylSL3_4)
    (td : TData (S : Subgroup G)) (hSn : (S : Subgroup G).Normal) : Concl G S := by
  have hD : pCore 2 G = (S : Subgroup G) := pCore_eq_sylow_of_normal S hSn
  have hC := centralizer_le_of_normal hO S td hSn
  have hidx := index_dvd_nine_of_normal hO S e td hSn
  have hBn : ∀ B : Subgroup G, B ≤ S → (∀ b ∈ B, b * b = 1) →
      (∀ b ∈ B, ∀ c ∈ B, b * c = c * b) → Nat.card B = 16 → B.Normal := by
    intro B hBS hsq hcomm hcard
    rcases elemAb16_eq td B hBS hsq hcomm hcard with rfl | rfl
    · exact A_normal_of_normal S td hSn
    · exact A_normal_of_normal S td.swap hSn
  unfold Concl
  refine ⟨?_, Or.inl ⟨hD, hidx, hBn⟩⟩
  rw [hD]
  exact hC

end CFSG.OddStandard.ThmC.O2
