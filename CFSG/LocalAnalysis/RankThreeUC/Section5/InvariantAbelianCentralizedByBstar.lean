module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.Context
import all CFSG.LocalAnalysis.RankThreeUC.Section5.Context
public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks
import CFSG.LocalAnalysis.RankThreeUC.Section5.NotIsPrimePowTwoPowSubOne
import CFSG.LocalAnalysis.RankThreeUC.Section5.TwoPowSubOneExponentDvd
import CFSG.RankThree.PartTwo.Sec13.Item136Transfer
public import CFSG.LocalAnalysis.RankThreeUC.Section5.HyperplaneOrbitStructure

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar

open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.RankThreeUC.Section5
  CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks
  CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations

section Generic

variable {H : Type} [Group H]

theorem le_of_forall_prime_orderOf_mem [Finite H] {C N : Subgroup H} (hsf : Squarefree (Nat.card C))
    (h : ∀ c ∈ C, (orderOf c).Prime → c ∈ N) : C ≤ N := by
  set K : Subgroup C := N.subgroupOf C with hK
  have hKtop : K = ⊤ := by
    by_contra hne
    have hidx : K.index ≠ 1 := fun h1 => hne (Subgroup.index_eq_one.mp h1)
    obtain ⟨q, hq, hqd⟩ := Nat.exists_prime_and_dvd hidx
    haveI : Fact q.Prime := ⟨hq⟩
    have hqC : q ∣ Nat.card C := hqd.trans K.index_dvd_card
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' q hqC
    have hcK : c ∈ K := by
      rw [hK, Subgroup.mem_subgroupOf]
      refine h c c.2 ?_
      rw [Subgroup.orderOf_coe, hc]
      exact hq
    have hqK : q ∣ Nat.card K := by
      have := orderOf_dvd_natCard (⟨c, hcK⟩ : K)
      rwa [Subgroup.orderOf_mk, hc] at this
    have hqq : q * q ∣ Nat.card C := by
      rw [← K.card_mul_index]
      exact Nat.mul_dvd_mul hqK hqd
    exact hq.one_lt.ne' (Nat.isUnit_iff.mp (hsf q hqq))
  intro c hc
  have : (⟨c, hc⟩ : C) ∈ K := by
    rw [hKtop]
    exact Subgroup.mem_top _
  exact this

theorem map_conj_mem_hyperplanes {E D : Subgroup H} {g : H} (hg : g ∈ Subgroup.normalizer (E : Set H))
    (hD : D ∈ hyperplanes 2 E) : D.map (MulAut.conj g).toMonoidHom ∈ hyperplanes 2 E := by
  have hmap : E.map (MulAut.conj g).toMonoidHom = E := Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  obtain ⟨hle, hidx⟩ := hD
  refine ⟨(Subgroup.map_mono hle).trans hmap.le, ?_⟩
  have := Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj g).toMonoidHom) D E (MulAut.conj g).injective
  rw [hmap] at this
  rw [this]
  exact hidx

theorem map_mem_commSpace {q : ℕ} {W : Type} [AddCommGroup W] [Module (ZMod q) W]
    (τ : Representation (ZMod q) H W) {E : Subgroup H} {g : H} (hg : g ∈ Subgroup.normalizer (E : Set H))
    {v : W} (hv : v ∈ commSpace τ E) : τ g v ∈ commSpace τ E := by
  unfold commSpace at hv ⊢
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, hx, u, rfl⟩ := hw
    refine Submodule.subset_span ⟨g * x * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg x).mp hx, τ g u, ?_⟩
    rw [map_sub, ← rho_mul_apply, ← rho_mul_apply, show g * x * g⁻¹ * g = g * x by group]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [map_smul]
    exact Submodule.smul_mem _ c hx

theorem conj_mul_inv_mem_of_relIndex_two {E D : Subgroup H} (hidx : D.relIndex E = 2)
    {g : H} (hgE : g ∈ Subgroup.normalizer (E : Set H)) (hgD : g ∈ Subgroup.normalizer (D : Set H))
    {x : H} (hx : x ∈ E) : g * x * g⁻¹ * x⁻¹ ∈ D := by
  have hidx' : (D.subgroupOf E).index = 2 := hidx
  have hgx : g * x * g⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hgE x).mp hx
  have key := (Subgroup.mul_mem_iff_of_index_two hidx' (a := ⟨g * x * g⁻¹, hgx⟩)
    (b := ⟨x⁻¹, E.inv_mem hx⟩)).mpr (by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact ((Subgroup.mem_normalizer_iff.mp hgD x).symm.trans inv_mem_iff.symm))
  exact key

theorem map_conj_eq_map_conj_iff (x y : H) (K : Subgroup H) :
    K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj y).toMonoidHom ↔
      y⁻¹ * x ∈ Subgroup.normalizer (K : Set H) := by
  have hmul : ∀ (a b : H) (L : Subgroup H), L.map (MulAut.conj (a * b)).toMonoidHom =
      (L.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
    intro a b L
    rw [Subgroup.map_map]
    congr 1
    ext z
    simp [MulAut.conj_apply, mul_assoc]
  have hone : ∀ L : Subgroup H, L.map (MulAut.conj (1 : H)).toMonoidHom = L := by
    intro L
    ext z
    simp [MulAut.conj_apply]
  have hN : y⁻¹ * x ∈ Subgroup.normalizer (K : Set H) ↔
      K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom = K := Subgroup.mem_normalizer_iff_map_conj_eq
  rw [hN]
  constructor
  · intro h
    rw [hmul, h, ← hmul, inv_mul_cancel, hone]
  · intro h
    calc K.map (MulAut.conj x).toMonoidHom = K.map (MulAut.conj (y * (y⁻¹ * x))).toMonoidHom := by
          rw [mul_inv_cancel_left]
      _ = K.map (MulAut.conj y).toMonoidHom := by rw [hmul, h]

theorem mem_normalizer_of_characteristic {S U : Subgroup H} (hUS : U ≤ S)
    (hchar : (U.subgroupOf S).Characteristic) {g : H} (hg : g ∈ Subgroup.normalizer (S : Set H)) :
    g ∈ Subgroup.normalizer (U : Set H) := by
  have key : ∀ k ∈ Subgroup.normalizer (S : Set H), ∀ u ∈ U, k * u * k⁻¹ ∈ U := by
    intro k hk u hu
    have hkS : ∀ s ∈ S, k * s * k⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.mp hk s).mp hs
    let φ : S ≃* S :=
      { toFun := fun s => ⟨k * s * k⁻¹, hkS s s.2⟩
        invFun := fun s => ⟨k⁻¹ * s * k, by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hk) s.1).mp s.2
          simpa using this⟩
        left_inv := fun s => by ext; simp [mul_assoc]
        right_inv := fun s => by ext; simp [mul_assoc]
        map_mul' := fun x y => by ext; simp [mul_assoc] }
    have h1 : Subgroup.comap φ.toMonoidHom (U.subgroupOf S) = U.subgroupOf S := hchar.fixed φ
    have h2 : (⟨u, hUS hu⟩ : S) ∈ Subgroup.comap φ.toMonoidHom (U.subgroupOf S) := by
      rw [h1]
      exact hu
    exact h2
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (Subgroup.inv_mem _ hg) _ hx
  simpa [mul_assoc] using this

end Generic

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem eq_one_of_sigma_fixes (hc : BinaryActionRankCounterexample G p P T B e ρ) {ψ : MulAut ↥P}
    (h : ∀ v : Space hc, sigma hc ψ v = v) : ψ = 1 := by
  refine MulEquiv.ext fun x => ?_
  have h1 := congrArg Space.val (h (Space.mk hc x))
  rw [sigma_apply] at h1
  exact h1

theorem mem_Bstar_iff (hP : P.Normal) {β : MulAut ↥P} : β ∈ Bstar P B ↔ ∃ b ∈ B, conjOnP P hP b = β := by
  rw [show Bstar P B = B.map (conjOnP P hP) from (image_eq P hP B).symm, Subgroup.mem_map]

theorem Bstar_commute (hc : BinaryActionRankCounterexample G p P T B e ρ) {β β' : MulAut ↥P}
    (hβ : β ∈ Bstar P B) (hβ' : β' ∈ Bstar P B) : β * β' = β' * β := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  obtain ⟨b, hb, rfl⟩ := (mem_Bstar_iff hP).mp hβ
  obtain ⟨b', hb', rfl⟩ := (mem_Bstar_iff hP).mp hβ'
  have hbb : b * b' = b' * b := by
    simpa using congrArg Subtype.val
      (hc.oddPrimeClassTwoAction.setting.abelian.is_comm.comm ⟨b, hb⟩ ⟨b', hb'⟩)
  rw [← map_mul, hbb, map_mul]

theorem sigma_fixed_transfer (hc : BinaryActionRankCounterexample G p P T B e ρ) {β β' : MulAut ↥P}
    (hβ : β ∈ Bstar P B) (hβ' : β' ∈ Bstar P B) (h1 : β ≠ 1) (h1' : β' ≠ 1) {v : Space hc}
    (hv : sigma hc β v = v) : sigma hc β' v = v := by
  have hP := hc.faithfulBinaryIrreducibleAction.normal
  obtain ⟨b, hb, rfl⟩ := (mem_Bstar_iff hP).mp hβ
  obtain ⟨b', hb', rfl⟩ := (mem_Bstar_iff hP).mp hβ'
  have hb1 : b ≠ 1 := by
    rintro rfl
    exact h1 (map_one _)
  have hb1' : b' ≠ 1 := by
    rintro rfl
    exact h1' (map_one _)
  have h520 := (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.1.2
  have hxv : b * ((v.val : ↥P) : G) * b⁻¹ = ((v.val : ↥P) : G) := by
    have := congrArg (fun u : Space hc => ((u.val : ↥P) : G)) hv
    simp only [sigma_apply, conjOnP_apply] at this
    exact this
  have hxC : ((v.val : ↥P) : G) ∈ P ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨(v.val).2, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    calc y * ((v.val : ↥P) : G) = (y * ((v.val : ↥P) : G) * y⁻¹) * y := by group
      _ = ((v.val : ↥P) : G) * y := by rw [hxv]
  rw [h520 b hb hb1, ← h520 b' hb' hb1'] at hxC
  have hb'x : b' * ((v.val : ↥P) : G) = ((v.val : ↥P) : G) * b' :=
    Subgroup.mem_centralizer_iff.mp hxC.2 b' rfl
  have : (((sigma hc (conjOnP P hP b') v).val : ↥P) : G) = ((v.val : ↥P) : G) := by
    rw [sigma_apply, conjOnP_apply, hb'x]
    group
  exact Additive.toMul.injective (Subtype.ext this)

theorem squarefree_card_Bstar (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Squarefree (Nat.card (Bstar P B)) := by
  have hcycB : IsCyclic ↥B :=
    (cyclic_actor_and_hyperplane_transitivity_and_irreducible_commutator_action hc).2.2.1
  have hsfB : Squarefree (Nat.card B) := by
    refine CFSG.GroupTheory.CoprimeActionSupport.FiniteCyclicPrimeSylowsComplement.squarefree_card (E := B) ?_
    intro q hq hqd
    have hqpi : q ∈ piOf B := ⟨hq, hqd⟩
    have h1 := hc.oddPrimeClassTwoAction.exponent_Or q hqpi
    unfold CFSG.Open.pCoreOf at h1
    exact (Monoid.exponent_eq_of_mulEquiv
      (Subgroup.equivMapOfInjective (CFSG.Open.pCore q B) B.subtype B.subtype_injective)).trans h1
  rw [BstarFaithful.card_eq hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction]
  exact hsfB

theorem exists_prime_ne_dvd_card_Bstar (hc : BinaryActionRankCounterexample G p P T B e ρ) (r : ℕ) :
    ∃ r' : ℕ, r'.Prime ∧ r' ∣ Nat.card (Bstar P B) ∧ r' ≠ r := by
  have h522 := not_isPrimePow_two_pow_sub_one hc
  have he : 2 ≤ e := hc.oddPrimeClassTwoAction.two_lt.le
  obtain ⟨r', hr', hdvd, hne⟩ := TwoPowSubOneExponentDvd.exists_prime_dvd_ne he h522 r
  have hpi : r' ∈ piOf B := by
    rw [hc.oddPrimeClassTwoAction.pi_eq]
    exact ⟨hr', hdvd⟩
  refine ⟨r', hr', ?_, hne⟩
  rw [BstarFaithful.card_eq hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction]
  exact hpi.2

theorem mem_normalizer_of_prime_orderOf (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {E : Subgroup (MulAut ↥P)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hN : Bstar P B ≤ Subgroup.normalizer (E : Set (MulAut ↥P)))
    (D : hyperplanes 2 E) (hD : commSpace (sigma hc) E ⊓ fixedSpace (sigma hc) D.1 ≠ ⊥)
    {a : MulAut ↥P} (ha : a ∈ Bstar P B) (har : (orderOf a).Prime) :
    a ∈ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) := by
  classical
  haveI : Fact p.Prime := ⟨CentralBinaryBlocks.prime hc⟩
  set σ := sigma hc with hσ
  set X : hyperplanes 2 E → Submodule (ZMod p) (Space hc) := fun K => commSpace σ E ⊓ fixedSpace σ K.1
    with hX
  have hind : iSupIndep X :=
    ProofSupport.BinaryCenterDecomposition.iSupIndep_inf (CentralBinaryDecomposition.p_ne_two hc) σ E hE
  set Y : Submodule (ZMod p) (Space hc) := ⨆ (K : hyperplanes 2 E) (_ : K ≠ D), X K with hYdef
  have hdisj : Disjoint (X D) Y := hind D
  have hcov : ∀ g (hg : g ∈ Subgroup.normalizer (E : Set (MulAut ↥P))) (K : hyperplanes 2 E), ∀ u ∈ X K,
      σ g u ∈ X ⟨K.1.map (MulAut.conj g).toMonoidHom, map_conj_mem_hyperplanes hg K.2⟩ := by
    intro g hg K u hu
    refine ⟨map_mem_commSpace σ hg hu.1, ?_⟩
    show σ g u ∈ fixedSpace σ (K.1.map (MulAut.conj g).toMonoidHom)
    rw [CentralBlockCovariance.fixedSpace_map_conj]
    exact Submodule.mem_map_of_mem hu.2
  have hY : ∀ g ∈ Subgroup.normalizer (E : Set (MulAut ↥P)), g ∉ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) →
      ∀ u ∈ X D, σ g u ∈ Y := by
    intro g hg hgD u hu
    have hne : (⟨D.1.map (MulAut.conj g).toMonoidHom, map_conj_mem_hyperplanes hg D.2⟩ : hyperplanes 2 E) ≠ D := by
      intro heq
      exact hgD (Subgroup.mem_normalizer_iff_map_conj_eq.mpr (congrArg Subtype.val heq))
    exact (le_iSup₂ (f := fun (K : hyperplanes 2 E) (_ : K ≠ D) => X K) _ hne) (hcov g hg D u hu)
  have hYD : ∀ u ∈ X D, u ∈ Y → u = 0 := fun u hu hu' =>
    (Submodule.disjoint_def.mp hdisj) u hu hu'
  by_contra haD
  set r := orderOf a with hr
  have haB : ∀ g ∈ Subgroup.zpowers a, g ∈ Bstar P B := fun g hg => (Subgroup.zpowers_le.mpr ha) hg
  have hrfree : ∀ g ∈ Subgroup.zpowers a, g ∈ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) → g = 1 := by
    intro g hg hgD
    by_contra hne
    have hord : orderOf g = r := by
      rcases (Nat.dvd_prime har).mp (orderOf_dvd_of_mem_zpowers hg) with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hne
      · exact h
    have heq : Subgroup.zpowers g = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hg)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hord])
    have haz : a ∈ Subgroup.zpowers g := by
      rw [heq]
      exact Subgroup.mem_zpowers a
    exact haD ((Subgroup.zpowers_le.mpr hgD) haz)
  obtain ⟨r', hr', hr'd, hrr'⟩ := exists_prime_ne_dvd_card_Bstar hc r
  haveI : Fact r'.Prime := ⟨hr'⟩
  obtain ⟨k₀, hk₀⟩ := exists_prime_orderOf_dvd_card' r' hr'd
  set k : MulAut ↥P := (k₀ : MulAut ↥P) with hkdef
  have hkB : k ∈ Bstar P B := k₀.2
  have hko : orderOf k = r' := by rw [hkdef, Subgroup.orderOf_coe, hk₀]
  have hk1 : k ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hko
    exact hr'.one_lt.ne hko
  have ha1 : a ≠ 1 := by
    intro h
    have h1 : r = 1 := by rw [hr, h, orderOf_one]
    rw [h1] at har
    exact Nat.not_prime_one har
  obtain ⟨w, hwX, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
  haveI : Fintype (Subgroup.zpowers a) := Fintype.ofFinite _
  set v : Space hc := ∑ g : Subgroup.zpowers a, σ g w with hv
  have hva : σ a v = v := by
    rw [hv, map_sum]
    refine Fintype.sum_equiv (Equiv.mulLeft (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a)) _ _
      (fun g => ?_)
    simp [rho_mul_apply]
  have hvk : σ k v = v := sigma_fixed_transfer hc ha hkB ha1 hk1 hva
  set S1 : Finset (Subgroup.zpowers a) := Finset.univ.erase 1 with hS1
  have hsplit : ∀ f : Subgroup.zpowers a → Space hc, ∑ g, f g = f 1 + ∑ g ∈ S1, f g := fun f =>
    (Finset.add_sum_erase Finset.univ f (Finset.mem_univ 1)).symm
  have hNE : ∀ g : Subgroup.zpowers a, (g : MulAut ↥P) ∈ Subgroup.normalizer (E : Set (MulAut ↥P)) :=
    fun g => hN (haB g g.2)
  have hgD : ∀ g : Subgroup.zpowers a, g ≠ 1 → (g : MulAut ↥P) ∉ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) :=
    fun g hg1 hgD => hg1 (Subtype.ext (hrfree g g.2 hgD))
  have hrest : ∑ g ∈ S1, σ (g : MulAut ↥P) w ∈ Y := by
    refine Submodule.sum_mem _ (fun g hg => ?_)
    exact hY g (hNE g) (hgD g (Finset.ne_of_mem_erase hg)) w hwX
  have hkN : k ∈ Subgroup.normalizer (E : Set (MulAut ↥P)) := hN hkB
  have hcomm : ∀ g : Subgroup.zpowers a, k * g = g * k := fun g => Bstar_commute hc hkB (haB g g.2)
  have hf : ∃ g₀ ∈ Subgroup.zpowers a, g₀⁻¹ * k ∈ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) := by
    by_contra hno
    push Not at hno
    have hkg : ∀ g : Subgroup.zpowers a, k * g ∉ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) := by
      intro g hkgD
      refine hno (g : MulAut ↥P)⁻¹ (Subgroup.inv_mem _ g.2) ?_
      rw [inv_inv, ← hcomm g]
      exact hkgD
    have hkv : σ k v ∈ Y := by
      rw [hv, map_sum]
      refine Submodule.sum_mem _ (fun g _ => ?_)
      rw [← rho_mul_apply]
      exact hY _ (Subgroup.mul_mem _ hkN (hNE g)) (hkg g) w hwX
    have hw : w = σ k v - ∑ g ∈ S1, σ (g : MulAut ↥P) w := by
      rw [hvk, hv, hsplit]
      simp
    exact hw0 (hYD w hwX (hw ▸ Submodule.sub_mem _ hkv hrest))
  obtain ⟨g₀, hg₀, hg₀k⟩ := hf
  have hkD : k ∈ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) := by
    have hpow : (g₀⁻¹ * k) ^ r' = g₀⁻¹ ^ r' := by
      have hc' : Commute g₀⁻¹ k :=
        (Bstar_commute hc (haB _ (Subgroup.inv_mem _ hg₀)) hkB)
      rw [hc'.mul_pow, ← hko, pow_orderOf_eq_one, mul_one]
    have h1 : g₀⁻¹ ^ r' = 1 :=
      hrfree _ (Subgroup.pow_mem _ (Subgroup.inv_mem _ hg₀) _)
        (hpow ▸ Subgroup.pow_mem _ hg₀k r')
    have h2 : g₀⁻¹ ^ r = 1 := by
      rw [hr, ← orderOf_dvd_iff_pow_eq_one]
      exact orderOf_dvd_of_mem_zpowers (Subgroup.inv_mem _ hg₀)
    have hcop : Nat.Coprime r' r := (Nat.coprime_primes hr' har).mpr hrr'
    have h3 : g₀⁻¹ = 1 := (pow_eq_one_iff_of_coprime hcop).mp ⟨h1, h2⟩
    rw [h3, one_mul] at hg₀k
    exact hg₀k
  have hkw : σ k w = w := by
    have hkg : ∀ g : Subgroup.zpowers a, g ≠ 1 → k * g ∉ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) := by
      intro g hg1 hkgD
      refine hgD g hg1 ?_
      have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hkD) hkgD
      rwa [inv_mul_cancel_left] at this
    have hdiff : σ k w - w ∈ Y := by
      have he : σ k w - w = ∑ g ∈ S1, σ (g : MulAut ↥P) w -
          ∑ g ∈ S1, σ (k * g) w := by
        have h1 : σ k v = σ k w + ∑ g ∈ S1, σ (k * g) w := by
          rw [hv, map_sum, hsplit]
          simp [rho_mul_apply]
        have h2 : v = w + ∑ g ∈ S1, σ (g : MulAut ↥P) w := by
          rw [hv, hsplit]
          simp
        have h3 : σ k w + ∑ g ∈ S1, σ (k * g) w = w + ∑ g ∈ S1, σ (g : MulAut ↥P) w := by
          rw [← h1, ← h2]
          exact hvk
        rw [sub_eq_sub_iff_add_eq_add, h3, add_comm]
      rw [he]
      refine Submodule.sub_mem _ hrest (Submodule.sum_mem _ (fun g hg => ?_))
      exact hY _ (Subgroup.mul_mem _ hkN (hNE g)) (hkg g (Finset.ne_of_mem_erase hg)) w hwX
    have hdX : σ k w - w ∈ X D := by
      refine Submodule.sub_mem _ ?_ hwX
      have h := hcov k hkN D w hwX
      have hDk : (⟨D.1.map (MulAut.conj k).toMonoidHom, map_conj_mem_hyperplanes hkN D.2⟩ :
          hyperplanes 2 E) = D := Subtype.ext (Subgroup.mem_normalizer_iff_map_conj_eq.mp hkD)
      rwa [hDk] at h
    exact sub_eq_zero.mp (hYD _ hdX hdiff)
  have haw : σ a w = w := sigma_fixed_transfer hc hkB ha hk1 ha1 hkw
  have := hY a (hN ha) haD w hwX
  rw [haw] at this
  exact hw0 (hYD w hwX this)

theorem Bstar_le_normalizer_of_ne_bot (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {E : Subgroup (MulAut ↥P)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hN : Bstar P B ≤ Subgroup.normalizer (E : Set (MulAut ↥P)))
    (D : hyperplanes 2 E) (hD : commSpace (sigma hc) E ⊓ fixedSpace (sigma hc) D.1 ≠ ⊥) :
    Bstar P B ≤ Subgroup.normalizer (D.1 : Set (MulAut ↥P)) :=
  le_of_forall_prime_orderOf_mem (squarefree_card_Bstar hc)
    (fun _ ha har => mem_normalizer_of_prime_orderOf hc hE hN D hD ha har)

theorem Bstar_le_centralizer_of_isElemAbelian (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {E : Subgroup (MulAut ↥P)} (hE : CFSG.Open.IsElemAbelian 2 E)
    (hN : Bstar P B ≤ Subgroup.normalizer (E : Set (MulAut ↥P))) :
    Bstar P B ≤ Subgroup.centralizer (E : Set (MulAut ↥P)) := by
  haveI : Fact p.Prime := ⟨CentralBinaryBlocks.prime hc⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp2 := CentralBinaryDecomposition.p_ne_two hc
  intro β hβ
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  set σ := sigma hc with hσ
  set y := β * x * β⁻¹ * x⁻¹ with hy
  have hyE : y ∈ E := E.mul_mem ((Subgroup.mem_normalizer_iff.mp (hN hβ) x).mp hx) (E.inv_mem hx)
  set M : Submodule (ZMod p) (Space hc) := LinearMap.ker (σ y - LinearMap.id) with hM
  have hmemM : ∀ u, u ∈ M ↔ σ y u = u := fun u => by
    rw [hM, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hblock : ∀ K : hyperplanes 2 E, commSpace σ E ⊓ fixedSpace σ K.1 ≤ M := by
    intro K u hu
    by_cases hK : commSpace σ E ⊓ fixedSpace σ K.1 = ⊥
    · rw [hK] at hu
      rw [(Submodule.mem_bot _).mp hu]
      exact M.zero_mem
    · have hβK := Bstar_le_normalizer_of_ne_bot hc hE hN K hK hβ
      have hyK : y ∈ K.1 := conj_mul_inv_mem_of_relIndex_two K.2.2 (hN hβ) hβK hx
      exact (hmemM u).mpr ((mem_fixedSpace_iff σ K.1 u).mp hu.2 y hyK)
  have hcomm : commSpace σ E ≤ M := by
    rw [← ProofSupport.BinaryCenterDecomposition.iSup_eq hp2 σ E hE]
    exact iSup_le hblock
  have hfix : fixedSpace σ E ≤ M := fun u hu =>
    (hmemM u).mpr ((mem_fixedSpace_iff σ E u).mp hu y hyE)
  have hcard : ((Nat.card E : ℕ) : ZMod p) ≠ 0 :=
    natCard_ne_zero_of_le (p := 2) (q := p) (fun h => hp2 h.symm) hE le_rfl
  have htop : (⊤ : Submodule (ZMod p) (Space hc)) ≤ M := by
    rw [← ProofSupport.CoprimeCommSpaceAveraging.split σ E hE.1 hcard]
    exact sup_le hcomm hfix
  have hy1 : y = 1 := eq_one_of_sigma_fixes hc (fun u => (hmemM u).mp (htop Submodule.mem_top))
  have hxβ : β * x * β⁻¹ = x := by
    rw [hy, mul_inv_eq_one] at hy1
    exact hy1
  calc x * β = (β * x * β⁻¹) * β := by rw [hxβ]
    _ = β * x := by group

theorem Bstar_le_centralizer_of_isMulCommutative (hc : BinaryActionRankCounterexample G p P T B e ρ)
    {U : Subgroup (MulAut ↥P)} (hU2 : IsPGroup 2 U) (hUab : IsMulCommutative U)
    (hN : Bstar P B ≤ Subgroup.normalizer (U : Set (MulAut ↥P))) :
    Bstar P B ≤ Subgroup.centralizer (U : Set (MulAut ↥P)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcommU : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hUab.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  let E : Subgroup (MulAut ↥P) :=
    { carrier := {x | x ∈ U ∧ x ^ 2 = 1}
      mul_mem' := fun {a b} ha hb => ⟨U.mul_mem ha.1 hb.1, by
        rw [(show Commute a b from hcommU a ha.1 b hb.1).mul_pow, ha.2, hb.2, one_mul]⟩
      one_mem' := ⟨U.one_mem, one_pow 2⟩
      inv_mem' := fun {a} ha => ⟨U.inv_mem ha.1, by rw [inv_pow, ha.2, inv_one]⟩ }
  have hmemE : ∀ x, x ∈ E ↔ x ∈ U ∧ x ^ 2 = 1 := fun _ => Iff.rfl
  have hE : CFSG.Open.IsElemAbelian 2 E :=
    ⟨⟨⟨fun a b => Subtype.ext (hcommU a ((hmemE a).mp a.2).1 b ((hmemE b).mp b.2).1)⟩⟩,
      fun x hx => ((hmemE x).mp hx).2⟩
  have hNE : Bstar P B ≤ Subgroup.normalizer (E : Set (MulAut ↥P)) := by
    intro β hβ
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [hmemE, hmemE]
    constructor
    · rintro ⟨hxU, hx2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hN hβ) x).mp hxU, ?_⟩
      rw [conj_pow, hx2, mul_one, mul_inv_cancel]
    · rintro ⟨hxU, hx2⟩
      refine ⟨(Subgroup.mem_normalizer_iff.mp (hN hβ) x).mpr hxU, ?_⟩
      rw [conj_pow] at hx2
      calc x ^ 2 = β⁻¹ * (β * x ^ 2 * β⁻¹) * β := by group
        _ = 1 := by rw [hx2]; group
  have hCE := Bstar_le_centralizer_of_isElemAbelian hc hE hNE
  have hodd := (CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction
    hc.faithfulBinaryIrreducibleAction).2.2.1
  intro β hβ
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hn : ¬ 2 ∣ orderOf β := fun h2 =>
    (Nat.not_even_iff_odd.mpr (Odd.of_dvd_nat hodd (Subgroup.orderOf_dvd_natCard _ hβ)))
      (even_iff_two_dvd.mpr h2)
  have hgn : ∀ z ∈ U, β ^ orderOf β * z * (β ^ orderOf β)⁻¹ = z := fun z _ => by
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one]
  have hfix : ∀ z ∈ U, z ^ 2 = 1 → β * z * β⁻¹ = z := fun z hz hz2 => by
    have h := Subgroup.mem_centralizer_iff.mp (hCE hβ) z ((hmemE z).mpr ⟨hz, hz2⟩)
    rw [← h]
    group
  have hxβ : β * x * β⁻¹ = x :=
    CFSG.RankThree.PartTwo.Sec13.conj_eq_of_coprime_pow (p := 2) hU2 hcommU (hN hβ) hn hgn hfix hx
  calc x * β = (β * x * β⁻¹) * β := by rw [hxβ]
    _ = β * x := by group

end CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar

namespace CFSG.LocalAnalysis.RankThreeUC.Section5

open CFSG.LocalAnalysis.RankThreeUC.Section5.InvariantAbelianCentralizedByBstar

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

theorem isSpecialPGroup_Sstar_and_center_eq_centralizer (hc : BinaryActionRankCounterexample G p P T B e ρ) :
    Section3.CoprimeSpecialGroups.IsSpecialPGroup (Sstar P T B) ∧
      (Subgroup.center (Sstar P T B)).map (Sstar P T B).subtype =
        Sstar P T B ⊓ Subgroup.centralizer (Bstar P B : Set (MulAut ↥P)) := by
  obtain ⟨hS2, hSne, hodd, hSB⟩ :=
    CoprimeStarSubgroupStructure.«structure» hc.oddPrimeClassTwoAction hc.faithfulBinaryIrreducibleAction
  have hcop : Nat.Coprime 2 (Nat.card (Bstar P B)) := (Nat.coprime_two_left).mpr hodd
  have hBS : Bstar P B ≤ Subgroup.normalizer (Sstar P T B : Set (MulAut ↥P)) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hSB.le
  rcases Section3.CoprimeSpecialGroups.exists_characteristic_abelian_not_centralized_or_special_center_eq_centralizer
      2 Nat.prime_two (Sstar P T B) (Bstar P B) hS2 hSne hcop hBS hSB with
    ⟨U, hUS, hchar, hUab, hnc⟩ | hres
  · exact absurd (Bstar_le_centralizer_of_isMulCommutative hc (hS2.to_le hUS) hUab
      (fun β hβ => mem_normalizer_of_characteristic hUS hchar (hBS hβ))) hnc
  · exact hres

end CFSG.LocalAnalysis.RankThreeUC.Section5
