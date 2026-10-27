module

public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6DExt
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EBridge
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6EGSide

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.UniquenessMaximal

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.Coordinator
  CFSG.HardMathSupport.Solomon.LocalBalance
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

section ExistsQ

theorem mem_normalizer_B_of_J {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {n : G} (hnJ : n ∈ jLayerOf L A)
    (hnF : n ∈ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G)) :
    n ∈ Subgroup.normalizer (B : Set G) := by
  have hnA : ∀ a ∈ A, n * a * n⁻¹ = a := by
    intro a ha
    have := Subgroup.mem_centralizer_iff.1 (jOf_le' L A hnJ).2 a ha
    rw [← this]; group
  have key : ∀ m ∈ jLayerOf L A, m ∈ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G) →
      ∀ y ∈ B, m * y * m⁻¹ ∈ B := by
    intro m hmJ hmF y hy
    have hy' : y ∈ A ⊔ (B ⊓ L) := by rw [hx.BAF]; exact hy
    have hle : A ⊔ (B ⊓ L) ≤ (B.comap (MulAut.conj m).toMonoidHom) := by
      refine sup_le (fun a ha => ?_) (fun f hf => ?_)
      · have := Subgroup.mem_centralizer_iff.1 (jOf_le' L A hmJ).2 a ha
        show m * a * m⁻¹ ∈ B
        rw [← this]; simpa using hx.AB ha
      · show m * f * m⁻¹ ∈ B
        exact ((Subgroup.mem_normalizer_iff.1 hmF f).1 hf).1
    exact hle hy'
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key n hnJ hnF y, fun hy => ?_⟩
  have h := key n⁻¹ (inv_mem hnJ) (inv_mem hnF) _ hy
  simpa [mul_assoc] using h

theorem centralizes_B_of_J {B : Subgroup G} {b : G} {L A : Subgroup G}
    (hx : ExtCtx B b L A) {n : G} (hnJ : n ∈ jLayerOf L A)
    (hnF : n ∈ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G)) :
    ∀ y ∈ B, n * y * n⁻¹ = y := by
  have hle : A ⊔ (B ⊓ L) ≤ Subgroup.centralizer ({n} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun f hf => ?_)
    · have := Subgroup.mem_centralizer_iff.1 (jOf_le' L A hnJ).2 a ha
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]; exact this.symm
    · rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]; exact (Subgroup.mem_centralizer_iff.1 hnF f hf).symm
  intro y hy
  have hy' : y ∈ A ⊔ (B ⊓ L) := by rw [hx.BAF]; exact hy
  have := Subgroup.mem_centralizer_iff.1 (hle hy') n (Set.mem_singleton n)
  rw [this]; group

theorem exists_Q {B : Subgroup G} {b : G} {L A : Subgroup G} (hw : LocalBalance.IsExtremalWitness B b L A)
    (hx : ExtCtx B b L A) :
    ∃ Q : Subgroup (MulAut ↥B), Q ≤ autIn B (jLayerOf L A) ∧ Nonempty (Q ≃* QuaternionGroup 2) ∧
      (∀ q ∈ Q, ∀ a ∈ inB B A, q a = a) ∧
      (∀ q ∈ Q, ∀ f ∈ inB B (B ⊓ L), q f ∈ inB B (B ⊓ L)) ∧
      (∀ q ∈ Q, (∀ f ∈ inB B (B ⊓ L), q f = f) → q = 1) := by
  obtain ⟨-, -, -, -, -, ⟨-, -, -, -, -, f, hf⟩, -⟩ := hw
  let f' : QuaternionGroup 2 →* autizer (jLayerOf L A) (B ⊓ L) := f
  have hf' : Function.Injective f' := hf
  have hle : jLayerOf L A ⊓ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G) ≤
      Subgroup.normalizer (B : Set G) := fun n hn => mem_normalizer_B_of_J hx hn.1 hn.2
  let ρ : ↥(jLayerOf L A ⊓ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G)) →* MulAut ↥B :=
    B.normalizerMonoidHom.comp (Subgroup.inclusion hle)
  have hρapp : ∀ (n : ↥(jLayerOf L A ⊓ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G))) (y : ↥B),
      ((ρ n y : ↥B) : G) = (n : G) * y * (n : G)⁻¹ := fun n y => rfl
  have hker : ∀ n, n ∈ ρ.ker → n ∈ (jLayerOf L A ⊓ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G)).subgroupOf
      (jLayerOf L A ⊓ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G)) := by
    intro n hn
    refine ⟨n.2.1, ?_⟩
    show (n : G) ∈ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have h2 : ρ n ⟨h, hh.1⟩ = ⟨h, hh.1⟩ := by rw [MonoidHom.mem_ker.1 hn]; rfl
    have h3 := congrArg Subtype.val h2
    rw [hρapp] at h3
    simp only at h3
    calc h * (n : G) = ((n : G) * h * (n : G)⁻¹) * (n : G) := by rw [h3]
      _ = (n : G) * h := by group
  have hsub : (jLayerOf L A ⊓ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G)).subgroupOf
      (jLayerOf L A ⊓ Subgroup.normalizer ((B ⊓ L : Subgroup G) : Set G)) ≤ ρ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext y
    rw [hρapp]
    exact centralizes_B_of_J hx n.2.1 hn.2 y y.2
  let ρ' : autizer (jLayerOf L A) (B ⊓ L) →* MulAut ↥B := QuotientGroup.lift _ ρ hsub
  have hρ' : Function.Injective ρ' := by
    rw [injective_iff_map_eq_one]
    intro z hz
    induction z using QuotientGroup.induction_on with
    | H n =>
      rw [QuotientGroup.eq_one_iff]
      exact hker n (by simpa [ρ'] using hz)
  have hinj : Function.Injective (ρ'.comp f') := hρ'.comp hf'
  refine ⟨(ρ'.comp f').range, ?_, ⟨(MonoidHom.ofInjective hinj).symm⟩, ?_, ?_, ?_⟩
  · intro q hq
    obtain ⟨c, rfl⟩ := hq
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f' c)
    refine Subgroup.mem_map.2 ⟨⟨n.1, hle n.2⟩, n.2.1, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [← hn]
    rfl
  · intro q hq a ha
    obtain ⟨c, rfl⟩ := hq
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f' c)
    simp only [MonoidHom.comp_apply]
    rw [← hn]
    apply Subtype.ext
    show (n : G) * a * (n : G)⁻¹ = a
    have := Subgroup.mem_centralizer_iff.1 (jOf_le' L A n.2.1).2 a ha
    rw [← this]; group
  · intro q hq f hf
    obtain ⟨c, rfl⟩ := hq
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f' c)
    simp only [MonoidHom.comp_apply]
    rw [← hn]
    show (n : G) * f * (n : G)⁻¹ ∈ B ⊓ L
    exact (Subgroup.mem_normalizer_iff.1 n.2.2 f).1 hf
  · intro q hq h
    obtain ⟨c, rfl⟩ := hq
    obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective (f' c)
    simp only [MonoidHom.comp_apply] at h ⊢
    rw [← hn] at h ⊢
    have : (QuotientGroup.mk n : autizer (jLayerOf L A) (B ⊓ L)) = 1 := by
      rw [QuotientGroup.eq_one_iff]
      refine ⟨n.2.1, ?_⟩
      show (n : G) ∈ Subgroup.centralizer ((B ⊓ L : Subgroup G) : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have h3 := congrArg Subtype.val (h ⟨g, hg.1⟩ hg)
      have h4 : (n : G) * g * (n : G)⁻¹ = g := h3
      calc g * (n : G) = ((n : G) * g * (n : G)⁻¹) * (n : G) := by rw [h4]
        _ = (n : G) * g := by group
    rw [this, map_one]

end ExistsQ

section Induced

variable {B U : Subgroup G}

@[expose] noncomputable def inducedHom (hN : U ≤ Subgroup.normalizer (B : Set G)) :
    ↥U →* MulAut ↥B :=
  B.normalizerMonoidHom.comp (Subgroup.inclusion hN)

theorem inducedHom_apply (hN : U ≤ Subgroup.normalizer (B : Set G)) (u : ↥U) (x : ↥B) :
    ((inducedHom hN u x : ↥B) : G) = (u : G) * x * (u : G)⁻¹ := rfl

@[expose] noncomputable def inducedP (hN : U ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup (MulAut ↥B) :=
  (inducedHom hN).range

theorem inducedP_le (hN : U ≤ Subgroup.normalizer (B : Set G)) : inducedP hN ≤ autIn B ⊤ := by
  rintro _ ⟨u, rfl⟩
  exact Subgroup.mem_map.2 ⟨⟨u.1, hN u.2⟩, Subgroup.mem_top _, rfl⟩

theorem inducedP_isPGroup {p : ℕ} [Fact p.Prime] (hN : U ≤ Subgroup.normalizer (B : Set G))
    (h : IsPGroup p ↥U) : IsPGroup p ↥(inducedP hN) :=
  h.of_surjective (inducedHom hN).rangeRestrict (inducedHom hN).rangeRestrict_surjective

theorem card_inducedP (hN : U ≤ Subgroup.normalizer (B : Set G)) :
    Nat.card ↥(inducedP hN) = (Subgroup.centralizer (B : Set G)).relIndex U := by
  have h1 : (inducedHom hN).ker = (Subgroup.centralizer (B : Set G)).subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff]
    constructor
    · intro h x hx
      have h2 := congrArg Subtype.val (DFunLike.congr_fun h ⟨x, hx⟩)
      rw [inducedHom_apply] at h2
      simp only [MulAut.one_apply] at h2
      calc x * (u : G) = ((u : G) * x * (u : G)⁻¹) * u := by rw [h2]
        _ = u * x := by group
    · intro h
      ext x
      rw [inducedHom_apply]
      have := h x x.2
      show (u : G) * x * (u : G)⁻¹ = x
      calc (u : G) * x * (u : G)⁻¹ = (u * x) * (u : G)⁻¹ := rfl
        _ = (x * u) * (u : G)⁻¹ := by rw [this]
        _ = x := by group
  rw [inducedP, ← Subgroup.index_ker, h1, Subgroup.relIndex]

theorem commutator_le_B (hN : U ≤ Subgroup.normalizer (B : Set G)) : ⁅U, B⁆ ≤ B := by
  rw [Subgroup.commutator_def]
  refine Subgroup.closure_le _ |>.2 ?_
  rintro _ ⟨u, hu, x, hx, rfl⟩
  show ⁅u, x⁆ ∈ B
  have h1 := (Subgroup.mem_normalizer_iff.1 (hN hu) x).1 hx
  rw [commutatorElement_def]
  exact B.mul_mem h1 (B.inv_mem hx)

theorem commB_inducedP (hN : U ≤ Subgroup.normalizer (B : Set G)) :
    commB (inducedP hN) = ⁅U, B⁆.subgroupOf B := by
  apply le_antisymm
  · refine Subgroup.closure_le _ |>.2 ?_
    rintro _ ⟨_, ⟨u, rfl⟩, x, rfl⟩
    show ((inducedHom hN u x * x⁻¹ : ↥B) : G) ∈ ⁅U, B⁆
    have : ((inducedHom hN u x * x⁻¹ : ↥B) : G) = ⁅(u : G), (x : G)⁆ := by
      rw [Subgroup.coe_mul, inducedHom_apply, commutatorElement_def]; rfl
    rw [this]
    exact Subgroup.commutator_mem_commutator u.2 x.2
  · intro y hy
    have hK : ⁅U, B⁆ ≤ (commB (inducedP hN)).map B.subtype := by
      rw [Subgroup.commutator_def]
      refine Subgroup.closure_le _ |>.2 ?_
      rintro _ ⟨u, hu, x, hx, rfl⟩
      refine ⟨inducedHom hN ⟨u, hu⟩ ⟨x, hx⟩ * (⟨x, hx⟩ : ↥B)⁻¹,
        Subgroup.subset_closure ⟨inducedHom hN ⟨u, hu⟩, ⟨_, rfl⟩, ⟨x, hx⟩, rfl⟩, ?_⟩
      show ((inducedHom hN ⟨u, hu⟩ ⟨x, hx⟩ * (⟨x, hx⟩ : ↥B)⁻¹ : ↥B) : G) = ⁅u, x⁆
      rw [Subgroup.coe_mul, inducedHom_apply, commutatorElement_def]; rfl
    obtain ⟨z, hz, hzy⟩ := hK hy
    have : z = y := Subtype.ext hzy
    rwa [← this]

theorem fixB_inducedP (hN : U ≤ Subgroup.normalizer (B : Set G)) :
    fixB (inducedP hN) = (B ⊓ Subgroup.centralizer (U : Set G)).subgroupOf B := by
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    refine ⟨y.2, fun u hu => ?_⟩
    have := congrArg Subtype.val (h _ ⟨⟨u, hu⟩, rfl⟩)
    rw [inducedHom_apply] at this
    calc u * (y : G) = ((u * y * u⁻¹) * u) := by group
      _ = y * u := by rw [show (u : G) * y * (u : G)⁻¹ = y from this]
  · rintro ⟨-, h⟩ p ⟨u, rfl⟩
    apply Subtype.ext
    rw [inducedHom_apply]
    have := h u u.2
    calc (u : G) * y * (u : G)⁻¹ = (u * y) * (u : G)⁻¹ := rfl
      _ = (y * u) * (u : G)⁻¹ := by rw [this]
      _ = y := by group

theorem card_subgroupOf_of_le {K : Subgroup G} (h : K ≤ B) : Nat.card ↥(K.subgroupOf B) = Nat.card ↥K :=
  Nat.card_congr (Subgroup.subgroupOfEquivOfLe h).toEquiv

end Induced

theorem le_of_subgroupOf_le {B K H : Subgroup G} (hK : K ≤ B)
    (h : K.subgroupOf B ≤ H.subgroupOf B) : K ≤ H := fun k hk =>
  (Subgroup.mem_subgroupOf.1 (h (Subgroup.mem_subgroupOf.2 hk) : (⟨k, hK hk⟩ : ↥B) ∈ H.subgroupOf B))

theorem lemma66v_transport (h65 : Lemma65) (h66 : Lemma66) {m : ℕ} (hS : GLStanding G m 3)
    (hC : GLCaseFour G 3) {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A)
    (hβ : ¬ ∀ u ∈ B, ∀ v ∈ B, u ≠ 1 → v ≠ 1 → ∃ g ∈ Subgroup.normalizer (B : Set G),
      g * u * g⁻¹ = v)
    (U : Subgroup G) (hN : U ≤ Subgroup.normalizer (B : Set G)) (h3 : IsPGroup 3 ↥U)
    (hc : Nat.card ↥⁅U, B⁆ = 3) :
    ((⁅U, B⁆ ≤ B ⊓ L ∧ A ≤ Subgroup.centralizer (U : Set G)) ∨
      (⁅U, B⁆ ≤ A ∧ B ⊓ L ≤ Subgroup.centralizer (U : Set G))) ∧
      Nat.card ↥(B ⊓ Subgroup.centralizer (U : Set G)) = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx := exists_extCtx hS hC hB hw
  obtain ⟨Q, hQ, hQ8, hfixA, hmemF, hfaith⟩ := exists_Q hw hx
  obtain ⟨h81, hexp, hcommB, hA9, hF9⟩ := bridge_facts hC hB hw
  have hQW : Q ≤ autIn B ⊤ := hQ.trans (autIn_mono le_top)
  have hsetup : Sec6E.Setup (autIn B ⊤) Q (inB B A) (inB B (B ⊓ L)) :=
    ⟨h81, hA9, hF9, hQW, hfixA, hmemF, hfaith, hQ8⟩
  obtain ⟨V, _, _, _, ⟨e⟩⟩ := exists_model hexp hcommB
  have hP3 := inducedP_isPGroup (p := 3) hN h3
  have hPW := inducedP_le hN
  have hC65 : Sec6E.Concl65 (autIn B ⊤) Q (inB B A) (inB B (B ⊓ L)) :=
    h65 G m hS hC B hB b L A hw Q hQ hQ8
  have key : ∀ p ∈ inducedP hN,
      Sec6E.glHom e p * (hsetup.datum e).t = (hsetup.datum e).t * Sec6E.glHom e p := by
    intro p hp
    have hpW := hPW hp
    rcases hC65 with hα | ⟨x, hxW, -, -, -, hperm, hlast⟩
    · have hn' : Sec6E.glHom e p ∈ Subgroup.normalizer
          ((Sec6E.gmap e Q : Subgroup (V ≃ₗ[ZMod 3] V)) : Set (V ≃ₗ[ZMod 3] V)) :=
        (Sec6E.mem_normalizer_gmap e).2 (hα hpW)
      exact (hsetup.datum e).comm_t_of_normalizes
        ((Subgroup.mem_normalizer_iff.1 hn' _).1 (hsetup.datum e).t_mem)
    · rcases hlast with hl | ⟨-, htrans⟩
      · have hperm' := hperm p ⟨hpW, hl hpW⟩
        obtain ⟨n, hn⟩ := hP3 ⟨p, hp⟩
        have hpn : p ^ (3 ^ n) = 1 := by simpa using congrArg Subtype.val hn
        refine (hsetup.datum e).comm_t_of_permutes (n := n) ?_ (by rw [← map_pow, hpn, map_one])
        unfold permutesAF at hperm'
        unfold Sec6E.Datum.PermutesAF
        simp only [Sec6E.Setup.datum_A, Sec6E.Setup.datum_F]
        rcases hperm' with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left
          exact ⟨by rw [← Sec6E.toSub_map, Sec6E.toSub_eq_iff]; exact h1,
            by rw [← Sec6E.toSub_map, Sec6E.toSub_eq_iff]; exact h2⟩
        · right
          exact ⟨by rw [← Sec6E.toSub_map, Sec6E.toSub_eq_iff]; exact h1,
            by rw [← Sec6E.toSub_map, Sec6E.toSub_eq_iff]; exact h2⟩
      · exfalso
        apply hβ
        intro u hu v hv hu1 hv1
        obtain ⟨w, hw', hwuv⟩ := htrans ⟨u, hu⟩ ⟨v, hv⟩
          (fun h => hu1 (congrArg Subtype.val h)) (fun h => hv1 (congrArg Subtype.val h))
        obtain ⟨⟨g, hg⟩, -, rfl⟩ := Subgroup.mem_map.1 hw'
        exact ⟨g, hg, congrArg Subtype.val hwuv⟩
  have hcommT : ∀ τ ∈ centerSub Q, ∀ p ∈ inducedP hN, p * τ = τ * p := by
    intro τ hτ p hp
    have hτ' : Sec6E.glHom e τ ∈ (hsetup.datum e).T := by
      rw [Sec6E.datum_T e hsetup]
      exact (Sec6E.glHom_mem_gmap e).2 hτ
    apply Sec6E.glHom_injective e
    rw [map_mul, map_mul]
    rcases (hsetup.datum e).T_cases hτ' with h | h
    · rw [h]; simp
    · rw [h]; exact (key p hp)
  obtain ⟨-, -, -, ⟨hidx, -⟩, hv⟩ :=
    h66 G m hS hC B hB b L A hw Q hQ hQ8 (inducedP hN) hPW hP3
  have hcard3 : Nat.card ↥(commB (inducedP hN)) = 3 := by
    rw [commB_inducedP hN, card_subgroupOf_of_le (commutator_le_B hN)]; exact hc
  have hv' := hv hcommT hcard3
  have hKB := commutator_le_B hN
  have hcomm' := commB_inducedP hN
  have hfix' := fixB_inducedP hN
  have hInfB : B ⊓ Subgroup.centralizer (U : Set G) ≤ Subgroup.centralizer (U : Set G) := inf_le_right
  refine ⟨?_, ?_⟩
  · rcases hv' with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · left
      refine ⟨le_of_subgroupOf_le hKB ?_, ?_⟩
      · rw [← hcomm']; exact h1
      · refine hInfB.trans' (le_of_subgroupOf_le hx.AB ?_)
        rw [← hfix']; exact h2
    · right
      refine ⟨le_of_subgroupOf_le hKB ?_, ?_⟩
      · rw [← hcomm']; exact h1
      · refine hInfB.trans' (le_of_subgroupOf_le (inf_le_left : B ⊓ L ≤ B) ?_)
        rw [← hfix']; exact h2
  · have h1 := Subgroup.card_mul_index (fixB (inducedP hN))
    rw [hidx, hcard3, hfix', card_subgroupOf_of_le inf_le_left, h81] at h1
    omega

theorem lemma66_transport (h66 : Lemma66) {m : ℕ} (hS : GLStanding G m 3) (hC : GLCaseFour G 3)
    {B : Subgroup G} (hB : IsBOneMax 3 B) {b : G} {L A : Subgroup G}
    (hw : IsExtremalWitness B b L A) (B₁ : Subgroup G)
    (hN : B₁ ≤ Subgroup.normalizer (B : Set G)) (h3 : IsPGroup 3 ↥B₁)
    (hc : Nat.card ↥⁅B₁, B⁆ ≤ 3) :
    (Subgroup.centralizer (B : Set G)).relIndex B₁ ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hx := exists_extCtx hS hC hB hw
  obtain ⟨Q, hQ, hQ8, -, -, -⟩ := exists_Q hw hx
  have hP3 := inducedP_isPGroup (p := 3) hN h3
  obtain ⟨-, ⟨hcard, -⟩, -, ⟨-, h9⟩, -⟩ :=
    h66 G m hS hC B hB b L A hw Q hQ hQ8 (inducedP hN) (inducedP_le hN) hP3
  have hcomm : Nat.card ↥(commB (inducedP hN)) = Nat.card ↥⁅B₁, B⁆ := by
    rw [commB_inducedP hN, card_subgroupOf_of_le (commutator_le_B hN)]
  rw [← card_inducedP hN]
  obtain ⟨n, hn⟩ := hP3.exists_card_eq
  rw [hn] at hcard h9 ⊢
  have hn2 : n ≤ 2 := by
    by_contra hcon
    have : 3 ^ 3 ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · norm_num
  · norm_num
  · have := h9 (by norm_num)
    omega

end CFSG.HardMathSupport.Solomon.UniquenessMaximal
