module

public import CFSG.Quasithin.H13.U3S1347V
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3S1347B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem s1347_A6_I_F4 (h1345 : NQS134.Stmt13_4_5_F4) (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hH₀M : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G))
    (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂)) (hZinf : cZ T H₁ ⊓ cZ T H₂ = ⊥) {K₀ : Subgroup G}
    (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    ∃ I : Subgroup G, ∃ _ : IsMulCommutative ↥I, I ≤ v0Of T H₁ H₂ ∧
      H₁ ⊔ H₂ ≤ normalizer (I : Set G) ∧ ¬ K₀ ≤ centralizer (I : Set G) ∧
      (∀ J : Subgroup G, J ≤ I → K₀ ≤ normalizer (J : Set G) → J = ⊥ ∨ J = I) ∧
      AlternatingNatural (V := ↥I) (autOn K₀ I) ⊤ ⊥ 6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hall⟩ := h1345 G T L V S (H₁ ⊔ H₂) hH₀ hH₀M hns
  obtain ⟨-, hN, -, -, -, -, -, ⟨I, hI⟩, hIall⟩ := hall K₀ hK₀
  obtain ⟨hTI, -, hIgen, ⟨hIc, hIcases⟩, -, -⟩ := hIall I hI
  obtain ⟨-, hIne, hKI, hIK, -, hIirr, -⟩ := hI
  have hKH := le_of_mem_cComp hK₀
  have hred := s1347_reduced S hH₀
  have hIV : I ≤ v0Of T H₁ H₂ := by
    have h1 : conjClosure (quasithinOmegaOneCenter T ⊓ I) K₀ ≤ v0Of T H₁ H₂ :=
      conjClosure_mono inf_le_left hKH
    rw [← hIgen] at h1
    exact h1
  have hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G) := hsup ▸ sup_le hKI hTI
  have hKIc : ¬ K₀ ≤ centralizer (I : Set G) := fun hle => hIne (by
    rw [← hIK]
    exact commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hle))
  have hs := (simple_of_cases (Or.inr (Or.inr hA6))).1
  have hO : pCoreOf 2 K₀ ≤ centralizer (I : Set G) :=
    (hcentK ▸ inf_le_right : pCoreOf 2 K₀ ≤ centralizer (v0Of T H₁ H₂ : Set G)).trans
      (centralizer_le (SetLike.coe_subset_coe.2 hIV))
  have hKC : K₀ ⊓ centralizer (I : Set G) = pCoreOf 2 K₀ := by
    refine le_antisymm (le_pCoreOf_of_normal inf_le_left (fun k hk => mem_normalizer_inf_of
      (le_normalizer hk) (mem_normalizer_centralizer_of_mem (hKI hk))) hs fun hle => ?_)
      (le_inf (pCoreOf_le 2 K₀) hO)
    exact hKIc (hle.trans (sup_le inf_le_right hO))
  have hcardK : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 360 := by
    obtain ⟨e⟩ := hA6
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hcardA : Nat.card (autOn K₀ I) = 360 := by
    rw [card_autOn_eq_relIndex hKI, hKC, ← hcardK, relIndex, pCoreOf_subgroupOf_eq_pCore]
    rfl
  rcases hIcases with ⟨h5, -⟩ | ⟨h6, hb⟩ | ⟨-, h2, -⟩ | ⟨hLie, -⟩
  ·
    exfalso
    obtain ⟨π, hπ, -⟩ := h5
    have hd : Nat.card (autOn K₀ I) ∣ Nat.card ↥(alternatingGroup (Fin 5)) :=
      card_dvd_of_surjective π hπ
    rw [hcardA, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hd
    exact absurd hd (by decide)
  · exact ⟨I, hIc, hIV, hH₀I, hKIc, fun J hJ hJK => by
      have := hIirr J (by rw [hb]; exact bot_le) hJ hJK
      rwa [hb] at this, h6⟩
  ·
    exfalso
    obtain ⟨z, hz, hz1⟩ := exists_ne_one_of_card_two h2
    have hTN : T ≤ normalizer (K₀ : Set G) := (hsup ▸ le_sup_right : T ≤ H₁ ⊔ H₂).trans hN
    have hzV := hIV (mem_inf.1 hz).1
    have hzT : ∀ t ∈ T, t * z = z * t := by
      intro t ht
      have htz : t * z * t⁻¹ ∈ I ⊓ centralizer (K₀ : Set G) :=
        (mem_normalizer_iff.1 (mem_normalizer_inf_of (hTI ht)
          (mem_normalizer_centralizer_of_mem (hTN ht))) z).1 hz
      rcases eq_one_or_eq_of_card_two h2 hz hz1 htz with h1 | h1
      · exfalso
        apply hz1
        calc z = t⁻¹ * (t * z * t⁻¹) * t := by group
          _ = 1 := by rw [h1]; group
      · calc t * z = t * z * t⁻¹ * t := by group
          _ = z * t := by rw [h1]
    have hzZ : z ∈ quasithinOmegaOneCenter T :=
      subset_closure ⟨⟨s1347_V0_le_T S hH₀ hzV, mem_centralizer_iff.2 hzT⟩, hred.2.2.1.2 z hzV⟩
    have hzC : ∀ g ∈ H₁ ⊔ H₂, g * z = z * g := by
      intro g hg
      rw [hsup] at hg
      obtain ⟨k, hk, t, ht, rfl⟩ := (B19Aux.mem_sup_iff_of_le_normalizer hTN).1 hg
      have hkz : k * z = z * k := mem_centralizer_iff.1 (mem_inf.1 hz).2 k hk
      calc k * t * z = k * (t * z) := by group
        _ = k * (z * t) := by rw [hzT t ht]
        _ = k * z * t := by group
        _ = z * k * t := by rw [hkz]
        _ = z * (k * t) := by group
    have hzH : z ∈ cZ T H₁ ⊓ cZ T H₂ :=
      mem_inf.2 ⟨mem_inf.2 ⟨hzZ, mem_centralizer_iff.2 fun g hg => hzC g (mem_sup_left hg)⟩,
        mem_inf.2 ⟨hzZ, mem_centralizer_iff.2 fun g hg => hzC g (mem_sup_right hg)⟩⟩
    rw [hZinf, mem_bot] at hzH
    exact hz1 hzH
  ·
    exfalso
    obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel hLie
    have := Nat.card_congr e.toEquiv
    rw [hcardK, HSType.card_SL_three_two] at this
    norm_num at this

theorem s1347_A6_data_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (h1345 : NQS134.Stmt13_4_5_F4) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂))
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hK₁ : oTwoRes H₁ ≤ K₀) (hK₂ : oTwoRes H₂ ≤ K₀) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    ∃ (I : Subgroup G) (_ : IsMulCommutative ↥I) (hH₀I : H₁ ⊔ H₂ ≤ normalizer (I : Set G))
      (ρ : ↥(H₁ ⊔ H₂) →* Perm (Fin 6)) (ψ : ↥I ≃* ↥W4) (F₀ : ↥(v0Of T H₁ H₂) →* ↥W4),
      I ≤ v0Of T H₁ H₂ ∧
      (∀ (g : ↥(H₁ ⊔ H₂)) (v : ↥I), ψ (conjAct I ⟨g, hH₀I g.2⟩ v) = act4 (ρ g) (ψ v)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), (g : G) ∈ T → InD6 (ρ g)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), (g : G) ∈ K₀ → ρ g ∈ alternatingGroup (Fin 6)) ∧
      (∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ centralizer (v0Of T H₁ H₂ : Set G)) ∧
      Function.Surjective F₀ ∧ (∀ v : ↥(v0Of T H₁ H₂), (v : G) ∈ I → F₀ v = 1) ∧
      ∀ (g : ↥(H₁ ⊔ H₂)) (v : ↥(v0Of T H₁ H₂)) (hv : (g : G) * v * (g : G)⁻¹ ∈ v0Of T H₁ H₂),
        (g : G) ∈ T ∨ (g : G) ∈ K₀ →
          F₀ ⟨g * v * (g : G)⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ g)) (F₀ v) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, hH₀M, -, hZsup, hZinf, hc₁, hc₂⟩ :=
    s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hKH := le_of_mem_cComp hK₀
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTH : T ≤ H₁ ⊔ H₂ := hsyl₀.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hsylK : IsSylowTwoOf (T ⊓ K₀) K₀ := A4.isSylowTwoOf_inf_normal hsyl₀ hKH hN
  obtain ⟨I, hIc, hIV, hH₀I, hKI, hIirr, hAN⟩ :=
    s1347_A6_I_F4 h1345 S hH₀ hH₀M hns hZinf hK₀ hA6 hsup hcentK
  obtain ⟨ρ, ψ, hψ, hρT, hρD, hρK⟩ := s1347_A6_frame hKH hN hH₀I hTH hT2 hsylK hAN
  have hs := (simple_of_cases (Or.inr (Or.inr hA6))).1
  have hCI := s1347_inf_centralizer_I S hH₀ hKH hN hsup hs hcentK hIV hH₀I hKI
  have hkerV : ∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ centralizer (v0Of T H₁ H₂ : Set G) := by
    intro g
    rw [s1347_rho_eq_one_iff hH₀I hψ]
    exact ⟨fun hg => hCI (mem_inf.2 ⟨g.2, hg⟩),
      fun hg => centralizer_le (SetLike.coe_subset_coe.2 hIV) hg⟩
  have hcent₀ := s1347_centralizer_eq_A6 S h hH₀ hN hsup hcentK
  have hkerO : ∀ g : ↥(H₁ ⊔ H₂), ρ g = 1 ↔ (g : G) ∈ pCoreOf 2 (H₁ ⊔ H₂) := by
    intro g
    rw [hkerV, ← hcent₀]
    exact ⟨fun hg => mem_inf.2 ⟨g.2, hg⟩, fun hg => (mem_inf.1 hg).2⟩
  have hρK' : ∀ k (hk : k ∈ K₀), ρ ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 6) := fun k hk =>
    (hρK _).1 ⟨k, hk, rfl⟩
  have h3₁ := s1347_relIndex_three S h.inH₁.1 h.s3₁
  have h3₂ := s1347_relIndex_three S h.inH₂.1 h.s3₂
  have hO₂T : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hnot : ∀ {Hi : Subgroup G}, T ≤ Hi → T.relIndex Hi = 3 →
      ¬ oTwoRes Hi ≤ pCoreOf 2 (H₁ ⊔ H₂) := by
    intro Hi hTi h3 hle
    have hsyl : IsSylowTwoOf T Hi := ⟨hTi, hT2, by
      show ¬ 2 ∣ T.relIndex Hi
      rw [h3]
      decide⟩
    have hHT : Hi ≤ T :=
      (le_oTwoRes_sup_of_isSylowTwoOf hsyl).trans (sup_le (hle.trans hO₂T) le_rfl)
    have h1 : T.relIndex Hi = 1 := relIndex_eq_one.2 hHT
    omega
  have hP₁ := s1347_A6_parabolic hT2 hTH hKH hkerO hρD hρK' le_sup_left h.inH₁.1 h3₁ hK₁
    (hnot h.inH₁.1 h3₁)
  have hP₂ := s1347_A6_parabolic hT2 hTH hKH hkerO hρD hρK' le_sup_right h.inH₂.1 h3₂ hK₂
    (hnot h.inH₂.1 h3₂)

  have hne : (H₁.subgroupOf (H₁ ⊔ H₂)).map ρ ≠ (H₂.subgroupOf (H₁ ⊔ H₂)).map ρ := by
    intro he
    apply h.ne
    have hk : ∀ {Hi : Subgroup G}, T ≤ Hi → ρ.ker ≤ Hi.subgroupOf (H₁ ⊔ H₂) := fun hTi g hg =>
      mem_subgroupOf.2 (hTi (hO₂T ((hkerO g).1 hg)))
    have hsub : H₁.subgroupOf (H₁ ⊔ H₂) = H₂.subgroupOf (H₁ ⊔ H₂) := by
      calc H₁.subgroupOf (H₁ ⊔ H₂) = comap ρ ((H₁.subgroupOf (H₁ ⊔ H₂)).map ρ) :=
            (comap_map_eq_self (hk h.inH₁.1)).symm
        _ = comap ρ ((H₂.subgroupOf (H₁ ⊔ H₂)).map ρ) := by rw [he]
        _ = H₂.subgroupOf (H₁ ⊔ H₂) := comap_map_eq_self (hk h.inH₂.1)
    have h1 := subgroupOf_inj.1 hsub
    rwa [inf_eq_left.2 le_sup_left, inf_eq_left.2 le_sup_right] at h1

  obtain ⟨u, hu, hu1⟩ := exists_ne_one_of_card_two hc₁
  obtain ⟨v, hv, hv1⟩ := exists_ne_one_of_card_two hc₂
  have hZ := s1347_Z_eq hZsup hc₁ hc₂ hu hu1 hv hv1
  have huZ : u ∈ quasithinOmegaOneCenter T := (mem_inf.1 hu).1
  have hvZ : v ∈ quasithinOmegaOneCenter T := (mem_inf.1 hv).1
  have hu₂ : u ∉ centralizer (H₂ : Set G) := fun h' => hu1 (by
    have : u ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨hu, mem_inf.2 ⟨huZ, h'⟩⟩
    rwa [hZinf, mem_bot] at this)
  have hv₁ : v ∉ centralizer (H₁ : Set G) := fun h' => hv1 (by
    have : v ∈ cZ T H₁ ⊓ cZ T H₂ := mem_inf.2 ⟨mem_inf.2 ⟨hvZ, h'⟩, hv⟩
    rwa [hZinf, mem_bot] at this)

  obtain ⟨F₀, hF₀s, hF₀I, hF₀T, hF₀K⟩ : ∃ F₀ : ↥(v0Of T H₁ H₂) →* ↥W4, Function.Surjective F₀ ∧
      (∀ v : ↥(v0Of T H₁ H₂), (v : G) ∈ I → F₀ v = 1) ∧
      (∀ t (ht : t ∈ T) (v : ↥(v0Of T H₁ H₂)) (hv : t * v * t⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨t * v * t⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨t, hTH ht⟩)) (F₀ v)) ∧
      (∀ k (hk : k ∈ K₀) (v : ↥(v0Of T H₁ H₂)) (hv : k * v * k⁻¹ ∈ v0Of T H₁ H₂),
        F₀ ⟨k * v * k⁻¹, hv⟩ = act4 (S6Out.phiEquiv.symm (ρ ⟨k, hKH hk⟩)) (F₀ v)) := by
    rcases hP₁ with h1 | h1
    · have h2 := hP₂.resolve_left fun h2 => hne (h1.trans h2.symm)
      exact s1347_A6_top S hH₀ hKH hN hsup hIV hH₀I hIirr hψ hTH hρT hρK hkerV le_sup_left
        h1 h2 hu hv hv₁ hZ
    · have h2 := hP₂.resolve_right fun h2 => hne (h1.trans h2.symm)
      refine s1347_A6_top S hH₀ hKH hN hsup hIV hH₀I hIirr hψ hTH hρT hρK hkerV le_sup_right
        h2 h1 hv hu hu₂ (fun z hz => ?_)
      rcases hZ z hz with h' | h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inr (Or.inl h'))
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inr (h'.trans (s1347_Z_comm huZ hvZ))))
  refine ⟨I, hIc, hH₀I, ρ, ψ, F₀, hIV, hψ, fun g hg => hρT g hg, fun g hg => hρK' g hg, hkerV,
    hF₀s, hF₀I, fun g w hw hg => ?_⟩
  rcases hg with hgT | hgK
  · exact hF₀T g hgT w hw
  · exact hF₀K g hgK w hw

theorem s1347_concl_iv_F4 (hedge : GoldschmidtEdgeBoundS3) (h1332 : Stmt13_3_2_F4)
    (h1228 : Stmt12_2_8_F4) (hC58 : TheoremC58) (h317 : AS317Sylow) (h56 : AsB56)
    (h135 : A6.Stmt13_3_5_F4) (h1345 : NQS134.Stmt13_4_5_F4) (S : A6.Setting134 G T L V)
    {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂) (hns : ¬ Group.IsSolvable ↥(H₁ ⊔ H₂))
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ cComp (H₁ ⊔ H₂)) (hN : H₁ ⊔ H₂ ≤ normalizer (K₀ : Set G))
    (hA6 : Nonempty (↥K₀ ⧸ CFSG.pCore 2 ↥K₀ ≃* alternatingGroup (Fin 6)))
    (hK₁ : oTwoRes H₁ ≤ K₀) (hK₂ : oTwoRes H₂ ≤ K₀) (hsup : H₁ ⊔ H₂ = K₀ ⊔ T)
    (hcentK : K₀ ⊓ centralizer (v0Of T H₁ H₂ : Set G) = pCoreOf 2 K₀) :
    Concl1347iv T H₁ H₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hH₀, -⟩ := s1347_one_first_F4 hedge h1332 h1228 hC58 h317 h56 h135 S h
  obtain ⟨I, hIc, hH₀I, ρ, ψ, F₀, hIV, hψ, hρT, -, hkerV, hF₀s, hF₀I, hF₀⟩ :=
    s1347_A6_data_F4 hedge h1332 h1228 hC58 h317 h56 h135 h1345 S h hns hK₀ hN hA6 hK₁ hK₂ hsup
      hcentK
  have hsyl₀ : IsSylowTwoOf T (H₁ ⊔ H₂) := A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1
  have hTH : T ≤ H₁ ⊔ H₂ := hsyl₀.1
  have hO₂T : pCoreOf 2 (H₁ ⊔ H₂) ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl₀
  have hred := s1347_reduced S hH₀
  have hI16 : Nat.card I = 16 := by
    rw [Nat.card_congr ψ.toEquiv]
    have h1 : Fintype.card {x : P6 // InW4 x} = 16 := by decide +kernel
    rw [← h1, ← Nat.card_eq_fintype_card]
    rfl

  have hoff : ∀ {j : ℕ}, j ≤ 1 → ∀ A, IsElemAbelianCorank T j A →
      A ≤ centralizer (v0Of T H₁ H₂ : Set G) := fun hj A hA =>
    le_centralizer_of_A6 hTH hred.2.2.1 (s1347_V0_le_T S hH₀) hIV hH₀I hI16 hψ
      (fun t ht => hρT ⟨t, hTH ht⟩ ht) hkerV hF₀s hF₀I
      (fun t ht x hx => hF₀ ⟨t, hTH ht⟩ x hx (Or.inl ht)) hj hA

  have hJ : ∀ {j : ℕ}, j ≤ 1 → H₁ ⊔ H₂ ≤ normalizer (thompsonJi T j : Set G) := fun hj =>
    le_normalizer_thompsonJi_of hO₂T (le_normalizer_pCoreOf 2 (H₁ ⊔ H₂)) fun A hA => by
      rw [← s1347_T_inf_centralizer S h hH₀]
      exact le_inf hA.1 (hoff hj A hA)
  exact ⟨K₀, hsup, hK₀, (quasithinO2QuotientIso_iff K₀ _).2 hA6, hJ (Nat.zero_le 1), hJ le_rfl⟩

end CFSG.Quasithin.H13.U3
