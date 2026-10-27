module

public import CFSG.GH74.Generic.BProg.B2.T1Basic
public import CFSG.GH74.Generic.BProg.B2.ShapeGenS13
public import CFSG.GH74.Generic.BProg.B2.U0Gen
public import CFSG.GH74.Generic.BProg.B1.Lift0

public section

namespace CFSG.GH74.Generic.BProg.B2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

namespace T1KleM

section Quot

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_mem_pPrimeCore {c : X} (hc : c ∈ pPrimeCore 2 X) {n : ℕ} (hcn : c ^ (2 ^ n) = 1) :
    c = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : orderOf c ∣ 2 ^ n := orderOf_dvd_of_pow_eq_one hcn
  have h2 : orderOf c ∣ Nat.card (pPrimeCore 2 X) := Subgroup.orderOf_dvd_natCard _ hc
  have h3 : orderOf c = 1 :=
    Nat.eq_one_of_dvd_coprimes ((CFSG.pPrimeCore_coprime_card (p := 2) (G := X)).pow_left n) h1 h2
  exact orderOf_eq_one_iff.1 h3

theorem odd_card_pPrimeCore : Odd (Nat.card (pPrimeCore 2 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.mp pPrimeCore_coprime_card

theorem card_map_mk_of_isPGroup {U : Subgroup X} (hU : IsPGroup 2 ↥U) :
    Nat.card ↥(U.map (QuotientGroup.mk' (pPrimeCore 2 X))) = Nat.card ↥U := by
  have : (pPrimeCore 2 X).Normal := pPrimeCore_normal
  let f := (QuotientGroup.mk' (pPrimeCore 2 X)).comp U.subtype
  have hf : Function.Injective f := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro u hu
    have hu' : (u : X) ∈ pPrimeCore 2 X := by
      have := (QuotientGroup.eq_one_iff (u : X)).1 hu
      exact this
    obtain ⟨n, hn⟩ := hU u
    have hn' : (u : X) ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
    exact (Subgroup.mem_bot).2 (Subtype.ext (eq_one_of_mem_pPrimeCore hu' hn'))
  have hrange : f.range = U.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

theorem eq_top_of_cover (M' : Subgroup X) (hN : pPrimeCore 2 X ≤ M') (S : Set (Subgroup X))
    (hS : ∀ U ∈ S, IsPGroup 2 ↥U) (hM : ∀ U ∈ S, centralizer (U : Set X) ≤ M')
    (hcov : (⨆ U ∈ S, centralizer ((U.map (QuotientGroup.mk' (pPrimeCore 2 X)) :
      Subgroup (X ⧸ pPrimeCore 2 X)) : Set (X ⧸ pPrimeCore 2 X))) = ⊤) : M' = ⊤ := by
  have : (pPrimeCore 2 X).Normal := pPrimeCore_normal
  have hodd : Odd (Nat.card (pPrimeCore 2 X)) := odd_card_pPrimeCore
  have h1 : (⨆ U ∈ S, centralizer ((U.map (QuotientGroup.mk' (pPrimeCore 2 X)) :
      Subgroup (X ⧸ pPrimeCore 2 X)) : Set (X ⧸ pPrimeCore 2 X))) ≤
      M'.map (QuotientGroup.mk' (pPrimeCore 2 X)) := by
    refine iSup₂_le fun U hU => ?_
    rw [← B1.map_centralizer_eq_centralizer_map_of_isPGroup (pPrimeCore 2 X) hodd (hS U hU)]
    exact Subgroup.map_mono (hM U hU)
  rw [hcov] at h1
  have h2 : M'.map (QuotientGroup.mk' (pPrimeCore 2 X)) = ⊤ := top_le_iff.1 h1
  have h3 := Subgroup.comap_map_eq (QuotientGroup.mk' (pPrimeCore 2 X)) M'
  rw [h2, Subgroup.comap_top, QuotientGroup.ker_mk', sup_eq_left.2 hN] at h3
  exact h3.symm

end Quot

section Setup

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem gammaK_le_M (hs : Stage2Setup G x K A M P Q) : gammaK 2 A 2 ≤ M := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have hr3 : pRank 2 ↥A = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hAcard)
  have h := (inU0_A hs).2.2
  rw [hr3] at h
  exact h

theorem centralizer_le_M_of_rank (hs : Stage2Setup G x K A M P Q) {V : Subgroup G} (hVA : V ≤ A)
    (hV : 2 ≤ pRank 2 ↥V) : centralizer (V : Set G) ≤ M := by
  intro g hg
  have h1 : g ∈ normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hg
  have h2 : normalizer (V : Set G) ≤ gammaK 2 A 2 := le_iSup₂_of_le V hVA (le_iSup_of_le hV le_rfl)
  exact gammaK_le_M hs (h2 h1)

theorem pPrimeCoreOf_le_M (hs : Stage2Setup G x K A M P Q) (hAK : A ≤ K ⊔ zpowers x) :
    pPrimeCoreOf 2 K ≤ M := by
  have hKnorm : K ≤ normalizer (pPrimeCoreOf 2 K : Set G) := fun k hk => by
    refine mem_normalizer_iff.2 fun n =>
      ⟨fun hn => TwoThin.pPrimeCoreOf_normalized K hk hn, fun hn => ?_⟩
    have := TwoThin.pPrimeCoreOf_normalized K (K.inv_mem hk) hn
    rwa [show k⁻¹ * (k * n * k⁻¹) * k⁻¹⁻¹ = n by group] at this
  have hKC : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  have hx : x ∈ normalizer (pPrimeCoreOf 2 K : Set G) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.2 fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.1 (hKC (TwoThin.pPrimeCoreOf_le K hn)))
  exact le_of_inU0_of_odd (inU0_A hs) (TwoThin.card_pPrimeCoreOf_odd K)
    (hAK.trans (sup_le hKnorm (zpowers_le.2 hx)))

end Setup

section S345

variable {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}

theorem K_le_M_s345 {Pr : ∀ (Kt : Type) [Group Kt], Prop} (hPr : ShapeGenFor Pr 4)
    (hs : Stage2Setup G x K A M P Q) {E : Subgroup G} (hEK : E ≤ K) (hAE : A = E ⊔ zpowers x)
    (hxE : x ∉ E) (hEel : CFSG.IsElementaryAbelian 2 ↥E) (hE4 : Nat.card ↥E = 4)
    (hPr' : Pr (↥K ⧸ pPrimeCore 2 ↥K)) : K ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2 : orderOf x = 2 := hs.pair.1.1.1.1
  have hKC : K ≤ centralizer ({x} : Set G) := hs.pair.1.1.1.2.2.1
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hEA : E ≤ A := hAE ▸ le_sup_left
  have hNM : pPrimeCoreOf 2 K ≤ M := pPrimeCoreOf_le_M hs (hAE ▸ sup_le_sup_right hEK _)
  have hNormal : (pPrimeCore 2 ↥K).Normal := pPrimeCore_normal
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥K)
  let E' : Subgroup ↥K := E.subgroupOf K
  have hE'el : CFSG.IsElementaryAbelian 2 ↥E' := IsElementaryAbelian.subgroupOf hEK
  have hE'card : Nat.card ↥E' = 4 := by
    rw [← hE4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hE'p : IsPGroup 2 ↥E' := CFSG.IsElementaryAbelian.isPGroup 2 ↥E'
  have hBel : CFSG.IsElementaryAbelian 2 ↥(E'.map π) := IsElementaryAbelian.map π
  have hBcard : Nat.card ↥(E'.map π) = 4 := (card_map_mk_of_isPGroup hE'p).trans hE'card
  have hgen := hPr _ hPr' (E'.map π) hBel hBcard
  let S : Set (Subgroup ↥K) := {U | ∃ b ∈ E', π b ∉ center (↥K ⧸ pPrimeCore 2 ↥K) ∧ U = zpowers b}
  have hb1 : ∀ b ∈ E', π b ∉ center (↥K ⧸ pPrimeCore 2 ↥K) → (b : G) ≠ 1 := by
    intro b _ hbZ hb
    have hb' : b = 1 := Subtype.ext hb
    exact hbZ (by rw [hb', map_one]; exact one_mem _)
  have hS : ∀ U ∈ S, IsPGroup 2 ↥U := by
    rintro U ⟨b, hb, -, rfl⟩
    exact hE'p.to_le (zpowers_le.2 hb)
  have hM : ∀ U ∈ S, centralizer (U : Set ↥K) ≤ M.comap K.subtype := by
    rintro U ⟨b, hb, hbZ, rfl⟩ k hk
    have hbk : (b : G) * k = k * b :=
      congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hk b (Subgroup.mem_zpowers b))
    have hbG : (b : G) ∈ E := Subgroup.mem_subgroupOf.1 hb
    have hbord : orderOf (b : G) = 2 :=
      ShapeGenS45.orderOf_eq_two_of_mem (B := E) hbG (hb1 b hb hbZ)
    have hbx : (b : G) ≠ x := fun h => hxE (h ▸ hbG)
    have hVA : closure ({(b : G), x} : Set G) ≤ A :=
      (Subgroup.closure_le A).2 (Set.insert_subset_iff.2 ⟨hEA hbG, Set.singleton_subset_iff.2 hxA⟩)
    have hcomm : (b : G) * x = x * (b : G) :=
      Subgroup.mem_centralizer_singleton_iff.1 (hKC b.2)
    have hrank : 2 ≤ pRank 2 ↥(closure ({(b : G), x} : Set G)) :=
      C3.Layer1.U1a.two_le_pRank_of_commute (subset_closure (by simp)) (subset_closure (by simp))
        hbord hx2 hcomm hbx
    refine centralizer_le_M_of_rank hs hVA hrank ?_
    rw [Subgroup.centralizer_closure]
    refine Subgroup.mem_centralizer_iff.2 fun h hh => ?_
    rcases hh with rfl | rfl
    · exact hbk
    · exact (Subgroup.mem_centralizer_singleton_iff.1 (hKC k.2)).symm
  have hcov : (⨆ U ∈ S, centralizer ((U.map π : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) :
      Set (↥K ⧸ pPrimeCore 2 ↥K))) = ⊤ := by
    refine top_le_iff.1 (hgen.symm.le.trans ?_)
    refine iSup₂_le fun b hb => ?_
    obtain ⟨⟨b', hb', rfl⟩, hbZ⟩ := hb
    refine le_iSup₂_of_le (zpowers b') ⟨b', hb', hbZ, rfl⟩ ?_
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have htop := eq_top_of_cover (M.comap K.subtype) (Subgroup.map_le_iff_le_comap.1 hNM) S hS hM hcov
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ M.comap K.subtype := htop ▸ Subgroup.mem_top _
  exact this

theorem K_le_M_s1 (h1 : GenConj QShape1 8) (hs : Stage2Setup G x K A M P Q) (hAK : A ≤ K)
    (hQ1 : QShape1 (↥K ⧸ pPrimeCore 2 ↥K)) : K ≤ M := by
  obtain ⟨-, hAel, hAcard, -⟩ := hs.src
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM : pPrimeCoreOf 2 K ≤ M := pPrimeCoreOf_le_M hs (hAK.trans le_sup_left)
  have hNormal : (pPrimeCore 2 ↥K).Normal := pPrimeCore_normal
  let π := QuotientGroup.mk' (pPrimeCore 2 ↥K)
  let A' : Subgroup ↥K := A.subgroupOf K
  have hA'el : CFSG.IsElementaryAbelian 2 ↥A' := IsElementaryAbelian.subgroupOf hAK
  have hA'card : Nat.card ↥A' = 8 := by
    rw [← hAcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv
  have hA'p : IsPGroup 2 ↥A' := CFSG.IsElementaryAbelian.isPGroup 2 ↥A'
  let B : Subgroup (↥K ⧸ pPrimeCore 2 ↥K) := A'.map π
  have hBel : CFSG.IsElementaryAbelian 2 ↥B := IsElementaryAbelian.map π
  have hBcard : Nat.card ↥B = 8 := (card_map_mk_of_isPGroup hA'p).trans hA'card
  have hrB : pRank 2 ↥B = 3 := pRank_eq_of_card_eq_pow one_lt_two (by simpa using hBcard)
  have hγ : gammaAct (ShapeGenS13.conjOn B) = ⊤ := h1 _ hQ1 B hBel hBcard
  let S : Set (Subgroup ↥K) :=
    {U | ∃ E : Subgroup ↥B, 2 ≤ pRank 2 ↥E ∧ U = A' ⊓ (E.map B.subtype).comap π}
  have hS : ∀ U ∈ S, IsPGroup 2 ↥U := by
    rintro U ⟨E, -, rfl⟩
    exact hA'p.to_le inf_le_left
  have hcov : (⨆ U ∈ S, centralizer ((U.map π : Subgroup (↥K ⧸ pPrimeCore 2 ↥K)) :
      Set (↥K ⧸ pPrimeCore 2 ↥K))) = ⊤ := by
    refine top_le_iff.1 (hγ.symm.le.trans ?_)
    rw [gammaAct]
    refine iSup₂_le fun E hE => ?_
    have hE2 : 2 ≤ pRank 2 ↥E := by rw [hrB] at hE; omega
    refine le_iSup₂_of_le (A' ⊓ (E.map B.subtype).comap π) ⟨E, hE2, rfl⟩ ?_
    intro y hy
    refine Subgroup.mem_centralizer_iff.2 fun s hs => ?_
    obtain ⟨u, ⟨-, e, he, hue⟩, rfl⟩ := hs
    have hfix := (GenLocBasic.mem_fixedIn_map (ShapeGenS13.conjOn B) E y).1 hy e he
    rw [ShapeGenS13.conjOn_apply, mul_inv_eq_iff_eq_mul] at hfix
    have hue' : π u = (e : ↥K ⧸ pPrimeCore 2 ↥K) := hue.symm
    rw [hue']
    exact hfix
  have hM : ∀ U ∈ S, centralizer (U : Set ↥K) ≤ M.comap K.subtype := by
    rintro U hUS k hk
    obtain ⟨E, hE2, rfl⟩ := hUS
    have hBc := hBel.1
    have hEA : CFSG.IsElementaryAbelian 2 ↥E :=
      WeakSigGen.isElementaryAbelian_of_forall (fun u _ v _ => mul_comm' u v)
        (fun u _ => WeakSigGen.mul_self_eq_one_of_isElementaryAbelian hBel u)
    have hEcard : Nat.card ↥E = 2 ^ pRank 2 ↥E := WeakSigGen.card_eq_two_pow_pRank hEA
    have hsub : E.map B.subtype ≤ (A' ⊓ (E.map B.subtype).comap π).map π := by
      rintro _ ⟨e, he, rfl⟩
      obtain ⟨a, ha, hae⟩ := e.2
      exact ⟨a, ⟨ha, ⟨e, he, hae.symm⟩⟩, hae⟩
    have hUcard : 4 ≤ Nat.card ↥(A' ⊓ (E.map B.subtype).comap π) := by
      have h1 := Subgroup.card_le_of_le hsub
      rw [Subgroup.card_map_of_injective B.subtype_injective, hEcard,
        card_map_mk_of_isPGroup (hS _ ⟨E, hE2, rfl⟩)] at h1
      have : 2 ^ 2 ≤ 2 ^ pRank 2 ↥E := Nat.pow_le_pow_right (by norm_num) hE2
      omega
    let V : Subgroup G := (A' ⊓ (E.map B.subtype).comap π).map K.subtype
    have hVA : V ≤ A := by
      rintro _ ⟨u, hu, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hu.1
    have hVel : CFSG.IsElementaryAbelian 2 ↥V := Th2Sig6.isElementaryAbelian_of_le hAel hVA
    have hVcard : Nat.card ↥V = Nat.card ↥(A' ⊓ (E.map B.subtype).comap π) :=
      Subgroup.card_map_of_injective K.subtype_injective
    have hVrank : 2 ≤ pRank 2 ↥V := by
      have h2 := Th2Sig6.card_eq_two_pow_pRank hVel
      rw [hVcard] at h2
      by_contra hlt
      have : 2 ^ pRank 2 ↥V ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    refine centralizer_le_M_of_rank hs hVA hVrank ?_
    refine Subgroup.mem_centralizer_iff.2 ?_
    rintro _ ⟨u, hu, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hk u hu)
  have htop := eq_top_of_cover (M.comap K.subtype) (Subgroup.map_le_iff_le_comap.1 hNM) S hS hM hcov
  intro k hk
  have : (⟨k, hk⟩ : ↥K) ∈ M.comap K.subtype := htop ▸ Subgroup.mem_top _
  exact this

end S345

end T1KleM

theorem K_le_M (h1 : GenConj QShape1 8) (h3 : ShapeGenFor QShape3 4) (h4 : ShapeGenFor QShape4 4)
    (h5 : ShapeGenFor QShape5 4) {G : Type} [Group G] [Finite G] {x : G} {K A M P Q : Subgroup G}
    (hs : Stage2Setup G x K A M P Q) : K ≤ M := by
  obtain ⟨-, -, -, hcase⟩ := hs.src
  rcases hcase with ⟨hAK, hQ1⟩ | ⟨E, hEK, hAE, hxE, hEel, hE4, hQ | hQ | hQ⟩
  · exact T1KleM.K_le_M_s1 h1 hs hAK hQ1
  · exact T1KleM.K_le_M_s345 h3 hs hEK hAE hxE hEel hE4 hQ
  · exact T1KleM.K_le_M_s345 h4 hs hEK hAE hxE hEel hE4 hQ
  · exact T1KleM.K_le_M_s345 h5 hs hEK hAE hxE hEel hE4 hQ

end CFSG.GH74.Generic.BProg.B2
