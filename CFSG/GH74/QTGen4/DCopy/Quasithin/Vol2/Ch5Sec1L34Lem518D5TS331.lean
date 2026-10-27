module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch5Sec1L34Lem518DLOS331
public import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem518D5T

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

section Setting

variable {G : Type} [Group G]

namespace Setting518D5

variable [CFSG.GH74.QTGen4.Finite4 G] {T M L V H B D D₃ D₅ : Subgroup G} {n : ℕ}
  (s : Setting518D5 G T M L V H B D D₃ D₅ n)
include s

theorem S_facts_F4 (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    s518 T H B D ≤ T ∧ T ⊓ L ≤ s518 T H B D ∧ T ⊓ oTwoUpper H ≤ s518 T H B D ∧
      pCoreOf 2 M ≤ s518 T H B D ∧
      pCoreOf 2 (Subgroup.normalizer (oTwoUpper H : Set G)) ≤ s518 T H B D ∧
      d518 H D ⊔ B ⊔ T ≤ Subgroup.normalizer (s518 T H B D : Set G) :=
  s.hyp.S_facts_of_le_F4 h510 h331 hR (d518_le H D) (d518_le_Mp H D)

theorem exists_two_parabolics_F4 (hTP : L34TwoParabolicFact) (hTA : L34TwoAutFact)
    (h510 : Stmt5_1_10_F4) (h331 : Stmt3_3_1_F4) (hR : L2RankOneSylowFact) :
    ∃ U₂ U₃ : Subgroup G, U₂ ≠ U₃ ∧ (∀ U : Subgroup G, (U = U₂ ∨ U = U₃) → ParData518 T H B D U) ∧
      oTwoUpper H ≤ oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₂ : Set G)) ⊔
        oTwoUpper (oTwoUpper H ⊓ Subgroup.normalizer (U₃ : Set G)) ∧
      ∀ g ∈ Subgroup.normalizer (oTwoUpper H : Set G),
        g ∈ Subgroup.normalizer ((T ⊓ oTwoUpper H : Subgroup G) : Set G) →
          (U₂.map (MulAut.conj g).toMonoidHom = U₂ ∨ U₂.map (MulAut.conj g).toMonoidHom = U₃) ∧
          (U₃.map (MulAut.conj g).toMonoidHom = U₂ ∨ U₃.map (MulAut.conj g).toMonoidHom = U₃) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := s.hyp
  set K := oTwoUpper H with hKdef
  set S := s518 T H B D with hSdef
  obtain ⟨hST, -, hTKS, -, -, hSN⟩ := s.S_facts_F4 h510 h331 hR
  obtain ⟨d₀, hd₀D, hd₀3, hd₀⟩ := s.exists_outer
  have hTK := h.isSylowTwoOf_inf_K
  have hOTK : pCoreOf 2 K ≤ T ⊓ K := CFSG.Quasithin.pCoreOf_le_of_isSylowTwoOf hTK
  have hBX : B ≤ d518 H D ⊔ B ⊔ T := le_sup_right.trans le_sup_left
  have hDX : d518 H D ≤ d518 H D ⊔ B ⊔ T := le_sup_left.trans le_sup_left
  have hXN := h.DBT_le_normalizer_inf_K_of_le_F4 h510 (d518_le H D) (d518_le_Mp H D)
  have hTMp := h.T_le_Mp
  obtain ⟨R₂, R₃, hne, hRfacts, hsup, hall⟩ :=
    hTP (O2Q K) h.l34 _ (isSylowTwoOf_imgO2 hTK)
  have hoddD : ∀ x ∈ d518 H D, Odd (orderOf x) := fun x hx =>
    h.notation59.2.1.2.1.of_dvd_nat
      (by rw [← Subgroup.orderOf_mk x ((d518_le H D) hx)]; exact orderOf_dvd_natCard _)
  have hoddB : ∀ x ∈ B, Odd (orderOf x) := fun x hx =>
    h.notation59.1.2.1.of_dvd_nat (by rw [← Subgroup.orderOf_mk x hx]; exact orderOf_dvd_natCard _)
  have hBK : B ≤ Subgroup.normalizer (K : Set G) :=
    h.notation59.1.1.trans (inf_le_right.trans (le_normalizer_oTwoUpper H))
  have hpar : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
      ParData518 T H B D (preimageModTwoCore K R) := by
    intro R hRR
    obtain ⟨hRS, hNSR, -, -, ⟨π, hπs, hπk⟩, -, hodd⟩ := hRfacts R hRR
    set U := preimageModTwoCore K R with hUdef
    have hUK : U ≤ K := preimageModTwoCore_le K R
    have hOU : pCoreOf 2 K ≤ U := pCoreOf_le_preimageModTwoCore K R
    have hUTK : U ≤ T ⊓ K :=
      (preimageModTwoCore_mono hRS).trans (preimageModTwoCore_imgO2 hOTK inf_le_right).le
    have hRU : imgO2 K U = R := imgO2_preimageModTwoCore K R
    have hoddN : ∀ g ∈ Subgroup.normalizer (K : Set G),
        g ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) → Odd (orderOf g) →
          g ∈ Subgroup.normalizer (U : Set G) := by
      intro g hgK hgT hgo
      apply mem_normalizer_preimageModTwoCore ⟨g, hgK⟩
      apply hodd
      · refine hgo.of_dvd_nat ((orderOf_map_dvd _ _).trans ?_)
        rw [Subgroup.orderOf_mk]
      · exact map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
    refine ⟨hOU, hUTK, ?_, ?_⟩
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        exact hoddN x ((d518_le_Mp H D) hx) (hXN (hDX hx)) (hoddD x hx)
      · intro x hx
        exact hoddN x (hBK hx) (hXN (hBX hx)) (hoddB x hx)
      · intro x hx
        have hxN : x ∈ Subgroup.normalizer (K : Set G) := hTMp (hST hx)
        obtain ⟨y, hy, hye⟩ := h.quotConjAut_eq_conj_of_mem_S_of_le_F4 hTA h510 h331 hR (d518_le H D)
          (d518_le_Mp H D) hd₀D hd₀3 hd₀ hx hxN
        apply mem_normalizer_preimageModTwoCore ⟨x, hxN⟩
        rw [hye]
        exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNSR (Subgroup.le_normalizer hy))
    ·
      have hP : ∀ x : ↥(K ⊓ Subgroup.normalizer (U : Set G)),
          ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left) x) ∈
            Subgroup.normalizer (R : Set (O2Q K)) := by
        intro x
        rw [← hRU]
        exact mk_mem_normalizer_imgO2 hUK x.2.1 x.2.2
      let ψ : ↥(K ⊓ Subgroup.normalizer (U : Set G)) →* ↥(Subgroup.normalizer (R : Set (O2Q K))) :=
        ((QuotientGroup.mk' (CFSG.pCore 2 ↥K)).comp (Subgroup.inclusion inf_le_left)).codRestrict
          _ hP
      refine ⟨π.comp ψ, ?_, ?_⟩
      · intro q
        obtain ⟨⟨y, hyP⟩, rfl⟩ := hπs q
        induction y using QuotientGroup.induction_on with
        | H k =>
          have hkN : (k : G) ∈ Subgroup.normalizer (U : Set G) := by
            refine mem_normalizer_preimageModTwoCore (K := K)
              (⟨(k : G), Subgroup.le_normalizer k.2⟩ : ↥(Subgroup.normalizer (K : Set G))) ?_
            rw [quotConjAut_of_mem k]
            exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hyP
          exact ⟨⟨k, k.2, hkN⟩, congrArg π (Subtype.ext rfl)⟩
      · ext x
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hπk,
          Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        constructor
        · intro hx
          exact mem_preimageModTwoCore.mpr ⟨x.2.1, hx⟩
        · intro hx
          exact (mem_preimageModTwoCore.mp hx).2
  refine ⟨preimageModTwoCore K R₂, preimageModTwoCore K R₃, ?_,
    fun U hU => ?_, ?_, ?_⟩
  · intro heq
    apply hne
    rw [← imgO2_preimageModTwoCore K R₂, heq, imgO2_preimageModTwoCore]
  · rcases hU with rfl | rfl
    · exact hpar R₂ (Or.inl rfl)
    · exact hpar R₃ (Or.inr rfl)
  ·
    set J := oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R₂ : Set G)) ⊔
      oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R₃ : Set G)) with hJ
    have himg : ∀ R : Subgroup (O2Q K), (R = R₂ ∨ R = R₃) →
        imgO2 K (oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R : Set G))) =
          Subgroup.normalizer (R : Set (O2Q K)) := by
      intro R hRR
      rw [imgO2_oTwoUpper inf_le_left, imgO2_inf_normalizer_preimage]
      exact (hRfacts R hRR).2.2.2.2.2.1
    have htop : imgO2 K J = ⊤ := by
      rw [eq_top_iff, ← hsup, ← himg R₂ (Or.inl rfl), ← himg R₃ (Or.inr rfl)]
      exact sup_le (Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)))
        (Subgroup.map_mono fun x hx =>
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)))
    have hOJ : pCoreOf 2 K ≤ Subgroup.normalizer (J : Set G) := by
      intro x hx
      have hxi : ∀ R : Subgroup (O2Q K), x ∈ Subgroup.normalizer
          (oTwoUpper (K ⊓ Subgroup.normalizer (preimageModTwoCore K R : Set G)) : Set G) := by
        intro R
        refine le_normalizer_oTwoUpper _ ⟨pCoreOf_le 2 K hx, ?_⟩
        exact Subgroup.le_normalizer (pCoreOf_le_preimageModTwoCore K R hx)
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, hJ, Subgroup.map_sup,
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hxi R₂),
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hxi R₃)]
    exact le_of_imgO2_eq_top rfl htop hOJ
  ·
    intro g hgK hgT
    have hα := map_quotConjAut_imgO2 inf_le_right ⟨g, hgK⟩ hgT
    obtain ⟨h2, h3⟩ := hall _ hα
    have e : ∀ R : Subgroup (O2Q K), (preimageModTwoCore K R).map (MulAut.conj g).toMonoidHom =
        preimageModTwoCore K (R.map (quotConjAut K ⟨g, hgK⟩).toMonoidHom) :=
      fun R => map_conj_preimageModTwoCore R ⟨g, hgK⟩
    refine ⟨?_, ?_⟩
    · rw [e]
      rcases h2 with h2 | h2 <;> rw [h2]
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [e]
      rcases h3 with h3 | h3 <;> rw [h3]
      · exact Or.inl rfl
      · exact Or.inr rfl

end Setting518D5

end Setting

end CFSG.Quasithin.H13
