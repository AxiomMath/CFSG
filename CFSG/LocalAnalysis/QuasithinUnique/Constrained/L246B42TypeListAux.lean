module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalSymplecticSix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeKVocab
public import CFSG.Quasithin.Background.B1MoreTenD
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso

public section

namespace CFSG.QuasithinUnique.Bridge.TypeList

open CFSG.Quasithin CFSG.Open
open scoped commutatorElement

theorem commutator_ne_top_of_card_six {G : Type*} [Group G] (h : Nat.card G = 6) :
    commutator G ≠ ⊤ := by
  have hfin : Finite G := Nat.finite_of_card_ne_zero (by omega)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [h]; norm_num : 3 ∣ Nat.card G)
  have hP : Nat.card (Subgroup.zpowers x) = 3 := by rw [Nat.card_zpowers, hx]
  have hidx : (Subgroup.zpowers x).index = 2 := by
    have h1 := (Subgroup.zpowers x).index_mul_card
    rw [h, hP] at h1
    omega
  have hPn : (Subgroup.zpowers x).Normal := Subgroup.normal_of_index_eq_two hidx
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic (G ⧸ Subgroup.zpowers x) := isCyclic_of_prime_card (p := 2) hidx
  have hcomm : ∀ a b : G ⧸ Subgroup.zpowers x, a * b = b * a :=
    isMulCommutative_iff.1 hcyc.isMulCommutative
  have hle : commutator G ≤ Subgroup.zpowers x := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : (QuotientGroup.mk' (Subgroup.zpowers x)) ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    exact (QuotientGroup.eq_one_iff _).1 h1
  intro htop
  rw [htop, top_le_iff] at hle
  rw [hle, Subgroup.index_top] at hidx
  omega

theorem exists_noncomm_of_quasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨-, -, a, b, hab⟩ := hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

theorem normal_eq_bot_or_alt_le {n : ℕ} (hn : 5 ≤ n) {M : Subgroup (Equiv.Perm (Fin n))}
    (hM : M.Normal) : M = ⊥ ∨ alternatingGroup (Fin n) ≤ M := by
  have hA : IsSimpleGroup (alternatingGroup (Fin n)) := alt_isSimple hn
  have hnM : (M.subgroupOf (alternatingGroup (Fin n))).Normal := hM.subgroupOf _
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (M.subgroupOf (alternatingGroup (Fin n)))
    with h | h
  · left
    rw [eq_bot_iff]
    intro m hm
    rw [Subgroup.mem_bot]
    have hcent : m ∈ Subgroup.centralizer
        (alternatingGroup (Fin n) : Set (Equiv.Perm (Fin n))) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 : a * m * a⁻¹ * m⁻¹ ∈ M :=
        M.mul_mem (hM.conj_mem m hm a) (M.inv_mem hm)
      have h2 : a * m * a⁻¹ * m⁻¹ ∈ alternatingGroup (Fin n) := by
        have := (alternatingGroup.normal (α := Fin n)).conj_mem a⁻¹
          ((alternatingGroup (Fin n)).inv_mem ha) m
        have h3 := (alternatingGroup (Fin n)).mul_mem ha this
        simpa [mul_assoc] using h3
      have h3 : (⟨a * m * a⁻¹ * m⁻¹, h2⟩ : alternatingGroup (Fin n)) ∈
          M.subgroupOf (alternatingGroup (Fin n)) := h1
      rw [h, Subgroup.mem_bot] at h3
      have h4 : a * m * a⁻¹ * m⁻¹ = 1 := congrArg Subtype.val h3
      calc a * m = (a * m * a⁻¹ * m⁻¹) * (m * a) := by group
        _ = m * a := by rw [h4, one_mul]
    rw [CFSG.ComponentClassification.PresentationLocal.centralizer_alternatingGroup_eq_bot
      (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; omega)] at hcent
    exact hcent
  · right
    intro a ha
    have : (⟨a, ha⟩ : alternatingGroup (Fin n)) ∈ M.subgroupOf (alternatingGroup (Fin n)) := by
      rw [h]; trivial
    exact this

theorem perm_perfect_normal_equiv {n : ℕ} (hn : 5 ≤ n) {H : Type} [Group H]
    (π : Equiv.Perm (Fin n) →* H) (hπ : Function.Surjective π) (L : Subgroup H) (hLn : L.Normal)
    (hperf : commutator ↥L = ⊤) (hnonab : ∃ a b : ↥L, a * b ≠ b * a) :
    Nonempty (alternatingGroup (Fin n) ≃* ↥L) := by
  have hcomm' : ∀ σ τ : Equiv.Perm (Fin n), ⁅σ, τ⁆ ∈ alternatingGroup (Fin n) := by
    intro σ τ
    rw [Equiv.Perm.mem_alternatingGroup, map_commutatorElement]
    exact commutatorElement_eq_one_iff_commute.2 (Commute.all _ _)
  rcases normal_eq_bot_or_alt_le hn π.normal_ker with hk | hk
  · have hinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).1 hk
    have hLn' : (L.comap π).Normal := hLn.comap π
    have hL1 : L.comap π ≠ ⊥ := by
      intro h
      obtain ⟨a, b, hab⟩ := hnonab
      apply hab
      have hone : ∀ x : ↥L, (x : H) = 1 := by
        intro x
        obtain ⟨σ, hσ⟩ := hπ (x : H)
        have hσL : σ ∈ L.comap π := by rw [Subgroup.mem_comap, hσ]; exact x.2
        rw [h, Subgroup.mem_bot] at hσL
        rw [← hσ, hσL, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul, hone a, hone b])
    rcases normal_eq_bot_or_alt_le hn hLn' with h | hAn
    · exact absurd h hL1
    · have hPL : (alternatingGroup (Fin n)).map π ≤ L := by
        rintro _ ⟨σ, hσ, rfl⟩
        exact hAn hσ
      have hLP : L ≤ (alternatingGroup (Fin n)).map π := by
        intro l hl
        have hle : commutator ↥L ≤ ((alternatingGroup (Fin n)).map π).subgroupOf L := by
          rw [commutator_def, Subgroup.commutator_le]
          intro x _ y _
          obtain ⟨σ, hσ⟩ := hπ (x : H)
          obtain ⟨τ, hτ⟩ := hπ (y : H)
          rw [Subgroup.mem_subgroupOf]
          refine ⟨⁅σ, τ⁆, hcomm' σ τ, ?_⟩
          rw [map_commutatorElement, hσ, hτ]
          simp [commutatorElement_def]
        have hmem : (⟨l, hl⟩ : ↥L) ∈ commutator ↥L := by rw [hperf]; trivial
        exact hle hmem
      have hEq : (alternatingGroup (Fin n)).map π = L := le_antisymm hPL hLP
      exact ⟨(Subgroup.equivMapOfInjective _ π hinj).trans (MulEquiv.subgroupCongr hEq)⟩
  · exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    apply hab
    obtain ⟨σ, hσ⟩ := hπ (a : H)
    obtain ⟨τ, hτ⟩ := hπ (b : H)
    have h1 : π ⁅σ, τ⁆ = 1 := MonoidHom.mem_ker.1 (hk (hcomm' σ τ))
    rw [map_commutatorElement, hσ, hτ] at h1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (commutatorElement_eq_one_iff_mul_comm.1 h1)

section G2

variable {K : Type} [Field K]

theorem zorn_eq_zero_of_shift [CharP K 2] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K}
    (hg : IsZornAuto g) {x : quasithinZorn K} (hx : x.1 + x.2.2.2 = 0) {c : K}
    (hc : g x = x + (c, 0, 0, c)) : c = 0 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hs : x.2.2.2 = x.1 := by
    have := eq_neg_of_add_eq_zero_right hx
    rw [this, CharTwo.neg_eq]
  set N : K := x.1 * x.1 + ∑ i, x.2.1 i * x.2.2.1 i with hN
  have hxx : quasithinZornMul x x = ((N, 0, 0, N) : quasithinZorn K) := by
    rw [zornMul_self]
    have h0 : x.1 + x.2.2.2 = 0 := hx
    refine Prod.ext rfl (Prod.ext ?_ (Prod.ext ?_ ?_))
    · simp [h0]
    · simp [h0]
    · simp only [hs, hN]
      congr 1
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hyy := hg x x
  rw [hxx, hg.map_smul_one, hc, zornMul_self] at hyy
  have h1 := congrArg Prod.fst hyy
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero] at h1
  have hcc : c * c = 0 := by
    linear_combination (-1 : K) * h1 + (-(x.1 * c)) * h2
  exact mul_self_eq_zero.mp hcc

theorem zorn_eq_one [CharP K 2] {g : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hg : IsZornAuto g)
    (h : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → ∃ c : K, g x = x + (c, 0, 0, c)) :
    g = 1 := by
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hfix : ∀ x : quasithinZorn K, x.1 + x.2.2.2 = 0 → g x = x := by
    intro x hx
    obtain ⟨c, hc⟩ := h x hx
    have hc0 : c = 0 := zorn_eq_zero_of_shift hg hx hc
    rw [hc, hc0]
    simp
  have hU : g ((0 : K), (![1, 0, 0] : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) =
      ((0 : K), (![1, 0, 0] : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) := hfix _ (by simp)
  have hV : g ((0 : K), (0 : Fin 3 → K), (![1, 0, 0] : Fin 3 → K), (0 : K)) =
      ((0 : K), (0 : Fin 3 → K), (![1, 0, 0] : Fin 3 → K), (0 : K)) := hfix _ (by simp)
  have hE : quasithinZornMul ((0 : K), (![1, 0, 0] : Fin 3 → K), (0 : Fin 3 → K), (0 : K))
      ((0 : K), (0 : Fin 3 → K), (![1, 0, 0] : Fin 3 → K), (0 : K)) =
      ((1 : K), (0 : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;>
      simp [quasithinZornMul, quasithinCross, Fin.sum_univ_three]
    all_goals (funext i; fin_cases i <;> simp)
  have hgE : g ((1 : K), (0 : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) =
      ((1 : K), (0 : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) := by
    rw [← hE, hg, hU, hV]
  apply LinearEquiv.ext
  intro x
  obtain ⟨r, u, v, s⟩ := x
  have hdec : ((r, u, v, s) : quasithinZorn K) =
      (r + s) • ((1 : K), (0 : Fin 3 → K), (0 : Fin 3 → K), (0 : K)) + s • zornOne +
        ((0 : K), u, v, (0 : K)) := by
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)) <;> simp [zornOne]
    linear_combination (-s) * h2
  have hz : g ((0 : K), u, v, (0 : K)) = ((0 : K), u, v, (0 : K)) := hfix _ (by simp)
  show g (r, u, v, s) = (r, u, v, s)
  rw [hdec, map_add, map_add, map_smul, map_smul, hgE, hg.map_one, hz]

theorem zornQ_faithful [CharP K 2] (Γ : Subgroup (quasithinZorn K ≃ₗ[K] quasithinZorn K))
    (hΓ : Γ ≤ quasithinG2 K) : (FFModel.zornQ Γ).Faithful := by
  intro (γ : ↥Γ) h
  have hg : IsZornAuto (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) :=
    mem_quasithinG2_isZornAuto (hΓ γ.2)
  have hone := zorn_eq_one hg fun x hx => by
    have hm : (Multiplicative.ofAdd x : Multiplicative (quasithinZorn K)) ∈ zornO0 K := hx
    obtain ⟨c, hc⟩ := h _ hm
    refine ⟨c, ?_⟩
    have hc2 : (γ : quasithinZorn K ≃ₗ[K] quasithinZorn K) x + -x = (c, 0, 0, c) := hc
    rw [← hc2]
    abel
  exact Subtype.ext hone

end G2

theorem exists_equiv_of_g2Natural {V : Type} [CommGroup V] {H : Subgroup (MulAut V)} {n : ℕ}
    (h : G2Natural H ⊤ ⊥ n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ n ∧
      Nonempty (↥(quasithinG2 K) ≃* ↥H) := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hcard : Fintype.card K = 2 ^ n := by rw [← Nat.card_eq_fintype_card, hc]
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h0 | h0
    · exfalso
      rw [h0, pow_zero] at hcard
      have := Fintype.one_lt_card (α := K)
      omega
    · exact h0
  have : CharP K 2 := charP_of_card_eq_prime_pow (p := 2) (f := n) hcard
  have hinj := hπ.injective_of_faithful (zornQ_faithful (K := K) _ le_rfl)
  exact ⟨K, hK, hf, hc, ⟨MulEquiv.ofBijective π ⟨hinj, hπ.1⟩⟩⟩

theorem ffJ_le_self {V : Type} [CommGroup V] (G : Subgroup (MulAut V)) : ffJ G ≤ G :=
  iSup₂_le fun _ hA => hA.1


theorem irr_of_isIrrSec {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (hirr : XMod.IsIrrSec ↥L (⊥ : Subgroup V) ⊤) :
    ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ := by
  intro J hJ
  have hinv : XMod.IsInv ↥L J := by
    intro l v hv
    have h2 : l • v = (l : MulAut V) v := by simp [Subgroup.smul_def, MulAut.smul_def]
    rw [h2]
    exact hJ l l.2 v hv
  exact hirr.2 J hinv bot_le le_top

theorem eq_one_of_commute_of_irr {V : Type} [CommGroup V] (hV : ∀ v : V, v ^ 2 = 1)
    {L : Subgroup (MulAut V)}
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {a : MulAut V} (ha2 : a ^ 2 = 1) (hcomm : ∀ l ∈ L, a * l = l * a) : a = 1 := by
  let C : Subgroup V :=
    { carrier := {v | a v = v}
      one_mem' := map_one a
      mul_mem' := fun {x y} hx hy => by
        show a (x * y) = x * y
        rw [map_mul, show a x = x from hx, show a y = y from hy]
      inv_mem' := fun {x} hx => by
        show a x⁻¹ = x⁻¹
        rw [map_inv, show a x = x from hx] }
  have hinv : ∀ l ∈ L, ∀ v ∈ C, l v ∈ C := by
    intro l hl v hv
    show a (l v) = l v
    have h1 : a (l v) = l (a v) := by
      have := congrArg (fun f : MulAut V => f v) (hcomm l hl)
      simpa [MulAut.mul_apply] using this
    rw [h1, show a v = v from hv]
  have hinvol : ∀ v : V, a (a v) = v := by
    intro v
    have : (a * a) v = v := by rw [← pow_two, ha2]; rfl
    simpa [MulAut.mul_apply] using this
  have hsq : ∀ w : V, w⁻¹ = w := fun w =>
    inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hV w)
  rcases hirr C hinv with hC | hC
  · refine MulEquiv.ext fun v => ?_
    have hmem : a v * v⁻¹ ∈ C := by
      show a (a v * v⁻¹) = a v * v⁻¹
      rw [map_mul, map_inv, hinvol, hsq (a v), hsq v, mul_comm]
    rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at hmem
    exact hmem
  · refine MulEquiv.ext fun v => ?_
    have hv : v ∈ C := by rw [hC]; trivial
    exact hv

theorem le_ffJ_of_b4Hyp {KP : ∀ (Y : Type) [Group Y], Prop} {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {G L A : Subgroup (MulAut V)} (hHyp : B4HypWith KP G L)
    (hA : IsFFStarOffender G A) : L ≤ ffJ G := by
  obtain ⟨-, hL, hq, hirr⟩ := hHyp
  have hLG : L ≤ G := by rw [hL]; exact CFSG.Quasithin.quasithinGenFitting_le G
  have hAN : A ≤ Subgroup.normalizer (L : Set (MulAut V)) := by
    intro a ha
    have := CFSG.Quasithin.le_normalizer_quasithinGenFitting G (hA.1 ha)
    rw [← hL] at this
    exact this
  have hne : ⁅L, A⁆ ≠ ⊥ := by
    intro hbot
    have hcomm : ∀ a ∈ A, ∀ l ∈ L, a * l = l * a := by
      intro a ha l hl
      have hmem : ⁅l, a⁆ ∈ ⁅L, A⁆ := Subgroup.commutator_mem_commutator hl ha
      rw [hbot, Subgroup.mem_bot] at hmem
      exact (commutatorElement_eq_one_iff_mul_comm.1 hmem).symm
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA.2.1
    have haA : (a : MulAut V) ∈ A := a.2
    have ha2 : (a : MulAut V) ^ 2 = 1 := hA.2.2.1.2 _ haA
    exact ha1 (Subtype.ext (eq_one_of_commute_of_irr hV (irr_of_isIrrSec hirr) ha2
      (hcomm _ haA)))
  exact B1Red.K_le_ffJ hLG hA (CFSG.QuasithinUnique.Setup.Layer.comm_eq_of_quasisimple hq hAN hne)

end CFSG.QuasithinUnique.Bridge.TypeList
