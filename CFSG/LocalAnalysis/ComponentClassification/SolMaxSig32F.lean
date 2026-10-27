module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig32E
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig35A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSigSwap

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

theorem le_pPrimeCore_of_normal_ne_top {T : Type*} [Group T] [Finite T]
    (hres : CatalogueBPrimeJoin.primeResidual 2 T = ⊤)
    (hsimp : IsSimpleGroup (T ⧸ pPrimeCore 2 T)) {N : Subgroup T} [N.Normal] (hN : N ≠ ⊤) :
    N ≤ pPrimeCore 2 T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.map (QuotientGroup.mk' (pPrimeCore 2 T))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (pPrimeCore 2 T)))
    with h | h
  · intro x hx
    have h1 : QuotientGroup.mk' (pPrimeCore 2 T) x ∈ N.map (QuotientGroup.mk' (pPrimeCore 2 T)) :=
      mem_map_of_mem _ hx
    rw [h, mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  · exfalso
    apply hN
    rw [eq_top_iff, ← hres]
    refine sSup_le fun P hP => ?_
    intro x hxP
    have h0 : QuotientGroup.mk' (pPrimeCore 2 T) x ∈
        N.map (QuotientGroup.mk' (pPrimeCore 2 T)) := by rw [h]; exact mem_top _
    obtain ⟨y, hy, hyx⟩ := h0
    have ho : y⁻¹ * x ∈ pPrimeCore 2 T := by
      rw [← QuotientGroup.eq]
      exact hyx
    set o := y⁻¹ * x with hodef
    have hxyo : x = y * o := by rw [hodef]; group
    obtain ⟨k, hk⟩ := hP ⟨x, hxP⟩
    have hk' : x ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have h1 : (QuotientGroup.mk' N o) ^ 2 ^ k = 1 := by
      have h2 := congrArg (QuotientGroup.mk' N) hk'
      have hyN : QuotientGroup.mk' N y = 1 := (QuotientGroup.eq_one_iff y).mpr hy
      rwa [hxyo, map_pow, map_mul, hyN, one_mul, map_one] at h2
    have h3 : orderOf (QuotientGroup.mk' N o) ∣ Nat.card (pPrimeCore 2 T) := by
      have h4 := orderOf_map_dvd (QuotientGroup.mk' N) o
      have h5 : orderOf o ∣ Nat.card (pPrimeCore 2 T) := by
        rw [← Subgroup.orderOf_mk o ho]
        exact orderOf_dvd_natCard _
      exact h4.trans h5
    have h6 : orderOf (QuotientGroup.mk' N o) = 1 := by
      have h7 : orderOf (QuotientGroup.mk' N o) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h7
      rcases j with _ | j
      · simpa using hj
      · exfalso
        rw [hj, pow_succ] at h3
        exact (Nat.not_even_iff_odd.mpr (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
          (even_iff_two_dvd.mpr (dvd_of_mul_left_dvd h3))
    rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h6
    rw [hxyo]
    exact mul_mem hy h6

theorem exists_coreQuot_equiv_of_hom {T : Type*} [Group T] [Finite T]
    (hres : CatalogueBPrimeJoin.primeResidual 2 T = ⊤) {k : ℕ} (hk : 5 ≤ k)
    (eT : T ⧸ pPrimeCore 2 T ≃* alternatingGroup (Fin k)) {A : Type*} [Group A] [Finite A]
    (φ : T →* A) (hφ : ∃ x, φ x ≠ 1) {Q : Subgroup A} (hQ : ∀ x, φ x ∈ Q)
    (hQc : Nat.card Q ≤ k.factorial / 2) :
    ∃ ψ : T ⧸ pPrimeCore 2 T ≃* Q, ∀ x : T, ((ψ (x : T ⧸ pPrimeCore 2 T) : Q) : A) = φ x := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (alternatingGroup (Fin k)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; omega)
  have hsimp : IsSimpleGroup (T ⧸ pPrimeCore 2 T) := MulEquiv.isSimpleGroup eT
  have hkerne : φ.ker ≠ ⊤ := by
    obtain ⟨x, hx⟩ := hφ
    intro h
    exact hx (h ▸ mem_top x : x ∈ φ.ker)
  have hkerO : φ.ker ≤ pPrimeCore 2 T := le_pPrimeCore_of_normal_ne_top hres hsimp hkerne
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have hTO : Nat.card T = Nat.card (pPrimeCore 2 T) * (k.factorial / 2) := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 T),
      Nat.card_congr eT.toEquiv, nat_card_alternatingGroup, Nat.card_fin, mul_comm]
  have hTk : Nat.card T = Nat.card φ.range * Nat.card φ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
  have hrQ : φ.range ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hQ x
  have hrc : Nat.card φ.range ≤ Nat.card Q := Subgroup.card_le_of_le hrQ
  have hkc : Nat.card φ.ker ≤ Nat.card (pPrimeCore 2 T) :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hkerO)
  have hOpos : 0 < Nat.card (pPrimeCore 2 T) := Nat.card_pos
  have hkpos : 0 < Nat.card φ.ker := Nat.card_pos
  have hkeq : Nat.card φ.ker = Nat.card (pPrimeCore 2 T) := by
    by_contra hne
    have hlt : Nat.card φ.ker < Nat.card (pPrimeCore 2 T) := lt_of_le_of_ne hkc hne
    have h1 : Nat.card φ.range * Nat.card φ.ker =
        Nat.card (pPrimeCore 2 T) * (k.factorial / 2) := by rw [← hTk, hTO]
    have h2 : Nat.card φ.range ≤ k.factorial / 2 := hrc.trans hQc
    have h3 : Nat.card φ.range * Nat.card φ.ker < Nat.card (pPrimeCore 2 T) * (k.factorial / 2) :=
      calc Nat.card φ.range * Nat.card φ.ker ≤ (k.factorial / 2) * Nat.card φ.ker :=
            Nat.mul_le_mul_right _ h2
        _ < (k.factorial / 2) * Nat.card (pPrimeCore 2 T) :=
            Nat.mul_lt_mul_of_pos_left hlt (by
              have := Nat.card_pos (α := alternatingGroup (Fin k))
              rwa [nat_card_alternatingGroup, Nat.card_fin] at this)
        _ = Nat.card (pPrimeCore 2 T) * (k.factorial / 2) := mul_comm _ _
    omega
  have hker : pPrimeCore 2 T = φ.ker :=
    (eq_of_le_of_card_ge hkerO (by rw [hkeq])).symm
  have hrange : φ.range = Q := by
    apply eq_of_le_of_card_ge hrQ
    have h1 : Nat.card φ.range * Nat.card φ.ker =
        Nat.card (pPrimeCore 2 T) * (k.factorial / 2) := by rw [← hTk, hTO]
    rw [hkeq, mul_comm] at h1
    have h2 := Nat.eq_of_mul_eq_mul_left hOpos h1
    rw [h2]
    exact hQc
  refine ⟨((QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivRange φ)).trans (MulEquiv.subgroupCongr hrange),
    fun x => ?_⟩
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  rfl

variable {X : Type} [Group X]

theorem le_normalizer_of_le_normalizer_sup [Finite X] {C L Y : Subgroup X} (hLC : L ≤ C)
    (hLpc : IsPComponent 2 (L.subgroupOf C)) (hYC : Y ≤ C)
    (hY : Y ≤ normalizer ((((pPrimeCore 2 ↥C).map C.subtype ⊔ L : Subgroup X)) : Set X)) :
    Y ≤ normalizer (L : Set X) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := (pPrimeCore 2 ↥C).map C.subtype with hOdef
  have hON : C ≤ normalizer (O : Set X) := Sol78.le_normalizer_map_subtype (pPrimeCore 2 ↥C)
  intro y hy
  rw [mem_normalizer_iff_map_conj_eq]
  by_contra hne
  set Ly := L.map (MulAut.conj y).toMonoidHom with hLydef
  obtain ⟨hLyC, hLypc⟩ := isPComponent_conj hLC hLpc (hYC hy)
  have hLyOL : Ly ≤ O ⊔ L := by
    have h1 : (O ⊔ L).map (MulAut.conj y).toMonoidHom = O ⊔ L :=
      (mem_normalizer_iff_map_conj_eq.mp (hY hy))
    rw [← h1]
    exact map_mono le_sup_right
  have hK : Ly ≤ UnbalancedLayer.coreActionKernel L :=
    GSThmB.B5a.le_coreActionKernel_of_ne hLC hLyC hLpc hLypc (Ne.symm hne)
  have hOL : (pPrimeCore 2 ↥L).map L.subtype ≤ O := pPrimeCore_le_of_isPComponent hLC hLpc
  have hcomm : ∀ a ∈ Ly, ∀ g ∈ O ⊔ L, a * g * a⁻¹ * g⁻¹ ∈ O := by
    intro a ha
    have haC : a ∈ C := hLyC ha
    let S : Subgroup X :=
      { carrier := {g | g ∈ C ∧ a * g * a⁻¹ * g⁻¹ ∈ O}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := by
          rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
          refine ⟨mul_mem hg hh, ?_⟩
          have h1 : g * (a * h * a⁻¹ * h⁻¹) * g⁻¹ ∈ O :=
            (mem_normalizer_iff.mp (hON hg) _).mp hh'
          have h2 : a * (g * h) * a⁻¹ * (g * h)⁻¹ =
              (a * g * a⁻¹ * g⁻¹) * (g * (a * h * a⁻¹ * h⁻¹) * g⁻¹) := by group
          rw [h2]
          exact mul_mem hg' h1
        inv_mem' := by
          rintro g ⟨hg, hg'⟩
          refine ⟨inv_mem hg, ?_⟩
          have h1 : g⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ ∈ O :=
            (mem_normalizer_iff.mp (hON (inv_mem hg)) _).mp (inv_mem hg')
          have h2 : a * g⁻¹ * a⁻¹ * g⁻¹⁻¹ = g⁻¹ * (a * g * a⁻¹ * g⁻¹)⁻¹ * g⁻¹⁻¹ := by group
          rw [h2]
          exact h1 }
    have hOS : O ≤ S := by
      intro g hg
      refine ⟨map_subtype_le _ hg, ?_⟩
      have h1 : a * g * a⁻¹ ∈ O := (mem_normalizer_iff.mp (hON haC) _).mp hg
      exact mul_mem h1 (inv_mem hg)
    have hLS : L ≤ S := by
      intro g hg
      refine ⟨hLC hg, hOL ?_⟩
      have h1 := (UnbalancedLayer.mem_coreActionKernel.mp (hK (inv_mem ha))).2 g⁻¹ (inv_mem hg)
      have h2 : (g⁻¹)⁻¹ * a⁻¹⁻¹ * g⁻¹ * a⁻¹ = g * a * g⁻¹ * a⁻¹ := by group
      rw [h2] at h1
      have h3 : a * g * a⁻¹ * g⁻¹ = (g * a * g⁻¹ * a⁻¹)⁻¹ := by group
      rw [h3]
      exact inv_mem h1
    intro g hg
    exact ((sup_le hOS hLS) hg).2
  have hLyperf : ⁅Ly, Ly⁆ = Ly := UnbalancedCorr.commutator_eq_of_isPComponent hLyC hLypc
  have hLyO : Ly ≤ O := by
    rw [← hLyperf, commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact hcomm a ha b (hLyOL hb)
  have hLyq : IsQuasisimple (↥Ly ⧸ pPrimeCore 2 ↥Ly) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 Ly C hLyC).mp hLypc).2.2
  have hodd : Nat.Coprime 2 (Nat.card Ly) := by
    have h1 : Nat.card Ly ∣ Nat.card O := card_dvd_of_le hLyO
    rw [hOdef, card_map_of_injective C.subtype_injective] at h1
    exact Nat.Coprime.coprime_dvd_right h1 pPrimeCore_coprime_card
  have htop : pPrimeCore 2 ↥Ly = ⊤ := by
    rw [eq_top_iff]
    exact le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩
  have : Nontrivial (↥Ly ⧸ pPrimeCore 2 ↥Ly) := LocalCores.isQuasisimple_nontrivial hLyq
  have : Subsingleton (↥Ly ⧸ pPrimeCore 2 ↥Ly) := QuotientGroup.subsingleton_iff.mpr htop
  exact false_of_nontrivial_of_subsingleton (↥Ly ⧸ pPrimeCore 2 ↥Ly)

theorem map_conjugate_subtype {Y : Subgroup X} {x : X} (hxY : x ∈ Y) (hx2 : x⁻¹ = x)
    (M : Subgroup ↥Y) :
    (conjugate M ⟨x, hxY⟩).map Y.subtype = (M.map Y.subtype).map (MulAut.conj x).toMonoidHom := by
  rw [conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext y
  simp [hx2]

theorem pump_type_in (hPump : Sol78.AlternatingPumpUpInput) [Finite X] {Y : Subgroup X}
    (hK : SectionRank.IsKGroupCat ↥Y) {x : X} (hxY : x ∈ Y) (hx : orderOf x = 2)
    {T : Subgroup X} (hTY : T ≤ Y ⊓ centralizer ({x} : Set X))
    (hTpc : IsPComponent 2 (T.subgroupOf (Y ⊓ centralizer ({x} : Set X)))) {k : ℕ} (hk : Odd k)
    (hk7 : 7 ≤ k) (eT : ↥T ⧸ pPrimeCore 2 ↥T ≃* alternatingGroup (Fin k)) :
    ∃ M : Subgroup X, M ≤ Y ∧ IsPComponent 2 (M.subgroupOf Y) ∧
      T ≤ M ⊔ M.map (MulAut.conj x).toMonoidHom ∧
      IsPComponent 2 (T.subgroupOf ((M ⊔ M.map (MulAut.conj x).toMonoidHom) ⊓
        centralizer ({x} : Set X))) ∧
      ((M.map (MulAut.conj x).toMonoidHom = M ∧
          ((∃ m' : ℕ, Odd m' ∧ k ≤ m' ∧
              Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin m'))) ∨
            (k = 7 ∧ Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* Blueprint.NativeSporadic.He)))) ∨
        (M.map (MulAut.conj x).toMonoidHom ≠ M ∧
          Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* alternatingGroup (Fin k)))) := by
  classical
  have hx2 : x⁻¹ = x := by
    have h1 : x * x = 1 := by rw [← sq, ← hx, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h1
  set x' : ↥Y := ⟨x, hxY⟩ with hx'def
  have hx' : orderOf x' = 2 := by rw [hx'def, Subgroup.orderOf_mk]; exact hx
  have hTYY : T ≤ Y := hTY.trans inf_le_left
  set T' := T.subgroupOf Y with hT'def
  have hcent : centralizer ({x'} : Set ↥Y) = (Y ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
    rw [centralizer_mk_eq hxY, inf_comm]
  have hT'C : T' ≤ centralizer ({x'} : Set ↥Y) := by
    rw [hcent]
    intro y hy
    exact hTY hy
  have hT'pc : IsPComponent 2 (T'.subgroupOf (centralizer ({x'} : Set ↥Y))) := by
    rw [hcent, hT'def, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two]
    exact hTpc
  let eT' : ↥T' ⧸ pPrimeCore 2 ↥T' ≃* alternatingGroup (Fin k) :=
    (Sol78.coreQuotCongr (subgroupOfEquivOfLe hTYY)).trans eT
  obtain ⟨M₀, hM₀pc, hTM₀, hTM₀pc, htype⟩ := pump_type hPump hK hx' hT'C hT'pc hk hk7 eT'
  set M := M₀.map Y.subtype with hMdef
  have hMY : M ≤ Y := map_subtype_le _
  have hMsub : M.subgroupOf Y = M₀ := by
    change (M₀.map Y.subtype).comap Y.subtype = M₀
    exact comap_map_eq_self_of_injective Y.subtype_injective M₀
  have hconj := map_conjugate_subtype hxY hx2 M₀
  rw [← hx'def] at hconj
  set Mx := M.map (MulAut.conj x).toMonoidHom with hMxdef
  have hsup : (M₀ ⊔ conjugate M₀ x').map Y.subtype = M ⊔ Mx := by
    rw [Subgroup.map_sup, hconj]
  have hMxY : Mx ≤ Y := by
    rw [← hconj]
    exact map_subtype_le _
  let φM : ↥M₀ ≃* ↥M := M₀.equivMapOfInjective Y.subtype Y.subtype_injective
  refine ⟨M, hMY, by rw [hMsub]; exact hM₀pc, ?_, ?_, ?_⟩
  · rw [← hsup]
    intro y hy
    exact ⟨⟨y, hTYY hy⟩, hTM₀ hy, rfl⟩
  ·
    have hle : (M ⊔ Mx) ⊓ centralizer ({x} : Set X) ≤ Y :=
      inf_le_left.trans (sup_le hMY hMxY)
    have heq : (M₀ ⊔ conjugate M₀ x') ⊓ centralizer ({x'} : Set ↥Y) =
        ((M ⊔ Mx) ⊓ centralizer ({x} : Set X)).subgroupOf Y := by
      rw [centralizer_mk_eq hxY, ← hsup]
      ext y
      simp only [mem_inf, mem_subgroupOf]
      constructor
      · rintro ⟨h1, h2, -⟩
        exact ⟨⟨y, h1, rfl⟩, h2⟩
      · rintro ⟨⟨z, hz, hzy⟩, h2⟩
        have hzy' : z = y := Subtype.ext hzy
        exact ⟨hzy' ▸ hz, h2, y.2⟩
    rw [heq] at hTM₀pc
    rw [← UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' hle 2 Nat.prime_two]
    exact hTM₀pc
  · have hfix_iff : conjugate M₀ x' = M₀ ↔ Mx = M := by
      constructor
      · intro h
        show Mx = M
        rw [← hconj, h]
      · intro h
        apply map_injective Y.subtype_injective
        show (conjugate M₀ x').map Y.subtype = M₀.map Y.subtype
        rw [hconj]
        exact h
    rcases htype with ⟨hfix, h⟩ | ⟨hne, ⟨eM⟩⟩
    · refine Or.inl ⟨hfix_iff.mp hfix, ?_⟩
      rcases h with ⟨m', hm', hkm', ⟨eM⟩⟩ | ⟨h7, ⟨eM⟩⟩
      · exact Or.inl ⟨m', hm', hkm', ⟨(Sol78.fusionZStarQuotCongr φM).symm.trans eM⟩⟩
      · exact Or.inr ⟨h7, ⟨(Sol78.fusionZStarQuotCongr φM).symm.trans eM⟩⟩
    · exact Or.inr ⟨fun h => hne (hfix_iff.mpr h), ⟨(Sol78.fusionZStarQuotCongr φM).symm.trans eM⟩⟩

end CFSG.ComponentClassification.SolMax
