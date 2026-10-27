module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma119
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13e
public import CFSG.LargeExtraspecial.S5Comp
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1110

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input223

open scoped commutatorElement

section Quasisimple

variable {H : Type*} [Group H]

theorem qs_nontrivial (hH : CFSG.Open.IsQuasisimple H) : Nontrivial H := by
  obtain ⟨-, hS⟩ := hH
  haveI := hS.toNontrivial
  exact Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center H))

theorem qs_comm_ne_bot (hH : CFSG.Open.IsQuasisimple H) : commutator H ≠ ⊥ := by
  haveI := qs_nontrivial hH
  rw [hH.1]
  exact top_ne_bot

theorem comm_central_mul_left {z : H} (hz : z ∈ Subgroup.center H) (a b : H) :
    ⁅z * a, b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have h1 : ⁅z, b⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hz' b).symm
  rw [commutatorElement_mul_left_eq_conj_mul, h1, mul_one, ← hz' ⁅a, b⁆, mul_assoc,
    mul_inv_cancel, mul_one]

theorem comm_central_mul_right {z : H} (hz : z ∈ Subgroup.center H) (a b : H) :
    ⁅a, z * b⁆ = ⁅a, b⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  have h1 : ⁅a, z⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.2 (hz' a)
  rw [commutatorElement_mul_right_eq_mul_conj, h1, one_mul, ← hz' ⁅a, b⁆, mul_assoc,
    mul_inv_cancel, mul_one]

theorem qs_normal_le_center (hH : CFSG.Open.IsQuasisimple H) (N : Subgroup H) [N.Normal]
    (hN : N ≠ ⊤) : N ≤ Subgroup.center H := by
  obtain ⟨hc, hS⟩ := hH
  rcases hS.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' (Subgroup.center H))) with h | h
  · intro x hx
    have hmem : (QuotientGroup.mk x : H ⧸ Subgroup.center H) ∈
        N.map (QuotientGroup.mk' (Subgroup.center H)) := ⟨x, hx, rfl⟩
    rw [h, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hmem
    exact hmem
  · exfalso
    have hcomm_le : commutator H ≤ N := by
      rw [commutator_def]
      refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
      have hdec : ∀ x : H, ∃ n ∈ N, ∃ z ∈ Subgroup.center H, x = n * z := by
        intro x
        have hx : (QuotientGroup.mk x : H ⧸ Subgroup.center H) ∈
            N.map (QuotientGroup.mk' (Subgroup.center H)) := by rw [h]; exact Subgroup.mem_top _
        obtain ⟨n, hn, hnx⟩ := hx
        refine ⟨n, hn, n⁻¹ * x, ?_, by group⟩
        have := QuotientGroup.eq.1 (show (QuotientGroup.mk n : H ⧸ Subgroup.center H) = QuotientGroup.mk x from hnx)
        exact this
      obtain ⟨n, hn, z, hz, rfl⟩ := hdec a
      obtain ⟨m, hm, w, hw, rfl⟩ := hdec b
      rw [(Subgroup.mem_center_iff.1 hz n), (Subgroup.mem_center_iff.1 hw m),
        comm_central_mul_left hz, comm_central_mul_right hw, commutatorElement_def]
      exact N.mul_mem (N.mul_mem (N.mul_mem hn hm) (N.inv_mem hn)) (N.inv_mem hm)
    rw [hc] at hcomm_le
    exact hN (top_le_iff.1 hcomm_le)

theorem qs_subnormal_aux {A B : Subgroup H} (hH : CFSG.Open.IsQuasisimple H)
    (h : CFSG.Open.IsSubnormal A B) : B = ⊤ → A ≠ ⊤ → A ≤ Subgroup.center H := by
  induction h with
  | refl A' => exact fun hB hA => absurd hB hA
  | @step X Y Z hle hn h2 ih =>
    intro hZ hX
    by_cases hY : Y = ⊤
    · subst hY
      have hnorm : X.Normal := by
        have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn
        rw [top_le_iff] at h1
        exact (Subgroup.normalizer_eq_top_iff).1 h1
      haveI := hnorm
      exact qs_normal_le_center hH X hX
    · exact hle.trans (ih hZ hY)

theorem qs_subnormal_le_center {M : Subgroup H} (hH : CFSG.Open.IsQuasisimple H)
    (h : CFSG.Open.IsSubnormal M ⊤) (hM : M ≠ ⊤) : M ≤ Subgroup.center H :=
  qs_subnormal_aux hH h rfl hM

end Quasisimple

section Components

variable {G : Type*} [Group G] [Finite G]

theorem comp_top_subgroupOf {L Y : Subgroup G} (hYL : CFSG.Open.IsComponentOf Y L) :
    CFSG.GorensteinWalter.IsComponentOf (Y.subgroupOf L) ⊤ :=
  (CFSG.Adapters.isComponentOf_top_iff _).1
    ((CFSG.LargeExtraspecial.S5.isComponentOf_iff_subgroupOf hYL.1).1 hYL)

theorem qs_not_comm_subgroup {Y : Subgroup G} (hY : CFSG.Open.IsQuasisimple ↥Y) :
    ¬ ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
  intro hc
  apply qs_comm_ne_bot hY
  rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a _
  rw [Subgroup.mem_centralizer_iff]
  intro b _
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  exact (hc a a.2 b b.2).symm

theorem comp_commute_normal {L Y K : Subgroup G} (hYL : CFSG.Open.IsComponentOf Y L)
    (hKL : CFSG.Open.IsComponentOf K L) (hKn : (K.subgroupOf L).Normal) (hYK : Y ≠ K) :
    ∀ y ∈ Y, ∀ k ∈ K, y * k = k * y := by
  have hdis := CFSG.GorensteinWalter.component_le_or_commutator_eq_bot_of_normal
    (comp_top_subgroupOf hYL) hKn
  rcases hdis with hle | hcomm
  · exfalso
    apply hYK
    have hYK' : Y ≤ K := by
      intro y hy
      have hyL : y ∈ L := hYL.1 hy
      have hu : (⟨y, hyL⟩ : L) ∈ Y.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
      exact Subgroup.mem_subgroupOf.1 (hle hu)
    have hsub : CFSG.Open.IsSubnormal Y K :=
      CFSG.LocalAnalysis.GLTheoremB.isSubnormal_of_le_of_le hYL.2.1 hYK' hKL.1
    by_contra hne
    apply qs_not_comm_subgroup hYL.2.2
    intro y hy y' hy'
    have hyK : y ∈ K := hYK' hy
    have hy'K : y' ∈ K := hYK' hy'
    have hsub' : CFSG.Open.IsSubnormal (Y.subgroupOf K) ⊤ :=
      (CFSG.LargeExtraspecial.S5.isSubnormal_subgroupOf_top_iff hYK').2 hsub
    have hne' : Y.subgroupOf K ≠ ⊤ := fun h => hne (le_antisymm hYK' (Subgroup.subgroupOf_eq_top.1 h))
    have hcen := qs_subnormal_le_center hKL.2.2 hsub' hne'
    have hyc : (⟨y, hyK⟩ : K) ∈ Subgroup.center K :=
      hcen (Subgroup.mem_subgroupOf.2 hy)
    have hc := Subgroup.mem_center_iff.1 hyc ⟨y', hy'K⟩
    have := congrArg Subtype.val hc
    exact this.symm
  · intro y hy k hk
    have hyL : y ∈ L := hYL.1 hy
    have hkL : k ∈ L := hKL.1 hk
    have hmem : (⟨y, hyL⟩ : L) ∈ Y.subgroupOf L := Subgroup.mem_subgroupOf.2 hy
    have hmem' : (⟨k, hkL⟩ : L) ∈ K.subgroupOf L := Subgroup.mem_subgroupOf.2 hk
    have hc := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm) hmem
    have hc' := Subgroup.mem_centralizer_iff.1 hc (⟨k, hkL⟩ : L) hmem'
    have := congrArg Subtype.val hc'
    exact this.symm

end Components

section PElement

variable {H : Type*} [Group H]

theorem exists_noncentral_pElt [Finite H] {p : ℕ} (hp : p.Prime)
    (hq : CFSG.Open.IsQuasisimple H) (hpH : p ∣ Nat.card H) :
    ∃ x : H, x ∉ Subgroup.center H ∧ ∃ n : ℕ, x ^ (p ^ n) = 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  let P : Sylow p H := default
  set Q : Subgroup H := (P : Subgroup H) with hQdef
  have hQc : Q ≤ Subgroup.center H := by
    intro x hx
    by_contra hxc
    obtain ⟨n, hn⟩ := P.2 ⟨x, hx⟩
    have hn' : x ^ (p ^ n) = 1 := by
      have := congrArg Subtype.val hn
      simpa using this
    exact hcon x hxc n hn'
  haveI hQn : Q.Normal := by
    constructor
    intro n hn g
    have hc := Subgroup.mem_center_iff.1 (hQc hn) g
    rw [show g * n * g⁻¹ = n by rw [hc, mul_inv_cancel_right]]
    exact hn
  have hcop : Nat.Coprime (Nat.card Q) Q.index := Sylow.card_coprime_index P
  obtain ⟨T, hT⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsplit : ∀ g : H, ∃ y ∈ Q, ∃ z ∈ T, y * z = g := by
    intro g
    have hg : g ∈ Q ⊔ T := by rw [hT.sup_eq_top]; exact Subgroup.mem_top g
    exact Subgroup.mem_sup_of_normal_left.1 hg
  have hTn : T.Normal := by
    constructor
    intro t ht g
    obtain ⟨y, hy, z, hz, rfl⟩ := hsplit g
    have hyc := Subgroup.mem_center_iff.1 (hQc hy)
    have e : y * z * t * (y * z)⁻¹ = z * t * z⁻¹ := by
      calc y * z * t * (y * z)⁻¹ = y * (z * t * z⁻¹) * y⁻¹ := by group
        _ = z * t * z⁻¹ := by
          rw [show y * (z * t * z⁻¹) * y⁻¹ = (z * t * z⁻¹) by
            rw [← Subgroup.mem_center_iff.1 (hQc hy) (z * t * z⁻¹)]; group]
    rw [e]
    exact T.mul_mem (T.mul_mem hz ht) (T.inv_mem hz)
  have hcomm : commutator H ≤ T := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
    obtain ⟨y, hy, z, hz, rfl⟩ := hsplit a
    obtain ⟨y', hy', z', hz', rfl⟩ := hsplit b
    have e1 := comm_central_mul_left (hQc hy) z (y' * z')
    have e2 := comm_central_mul_right (hQc hy') z z'
    rw [e1, e2, commutatorElement_def]
    exact T.mul_mem (T.mul_mem (T.mul_mem hz hz') (T.inv_mem hz)) (T.inv_mem hz')
  rw [hq.1] at hcomm
  have hT_top : T = ⊤ := top_le_iff.1 hcomm
  have hQbot : Q = ⊥ := by
    have hd := hT.disjoint
    rw [hT_top] at hd
    exact disjoint_top.1 hd
  have hcardH : Nat.card H = Q.index := by
    rw [hQbot, Subgroup.index_bot]
  exact P.not_dvd_index (hcardH ▸ hpH)

end PElement

section CentralProduct

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

structure CPData (p : ℕ) (B L : Subgroup G) (𝓛 : Set (Subgroup G)) : Prop where
  elem : CFSG.Open.IsElemAbelian p B
  norm : B ≤ Subgroup.normalizer (L : Set G)
  comp : ∀ K ∈ 𝓛, CFSG.Open.IsComponentOf K L
  gen : L = sSup 𝓛
  comm : ∀ K ∈ 𝓛, ∀ K' ∈ 𝓛, K ≠ K' → ∀ x ∈ K, ∀ y ∈ K', x * y = y * x
  trans : ∀ K ∈ 𝓛, ∀ K' ∈ 𝓛, ∃ b ∈ B, GLBConj b K = K'

theorem normalizer_of_comm (K : Subgroup G) (x : G) (hx : ∀ h ∈ K, x * h = h * x) :
    x ∈ Subgroup.normalizer (K : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have h1 : x * h * x⁻¹ = h := by rw [hx h hh, mul_inv_cancel_right]
    rw [h1]
    exact hh
  · intro hh
    have h3 : x⁻¹ * (x * h * x⁻¹) * x = x * h * x⁻¹ := by
      calc x⁻¹ * (x * h * x⁻¹) * x = x⁻¹ * ((x * h * x⁻¹) * x) := by group
        _ = x⁻¹ * (x * (x * h * x⁻¹)) := by rw [← hx _ hh]
        _ = x * h * x⁻¹ := by group
    have h5 : x⁻¹ * (x * h * x⁻¹) * x = h := by group
    rw [h3] at h5
    rw [← h5]
    exact hh

theorem CPData.K_le_L {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K : Subgroup G} (hK : K ∈ 𝓛) : K ≤ L :=
  (hcp.comp K hK).1

theorem CPData.K_normal {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K : Subgroup G} (hK : K ∈ 𝓛) : (K.subgroupOf L).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer (hcp.K_le_L hK), hcp.gen]
  refine sSup_le fun K' hK' => ?_
  by_cases hKK : K' = K
  · subst hKK
    exact Subgroup.le_normalizer
  · intro x hx
    exact normalizer_of_comm K x (fun h hh => hcp.comm K' hK' K hK hKK x hx h hh)

theorem CPData.comp_mem {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {Y : Subgroup G} (hY : CFSG.Open.IsComponentOf Y L) : Y ∈ 𝓛 := by
  by_contra hY𝓛
  have hcen : L ≤ Subgroup.centralizer (Y : Set G) := by
    rw [hcp.gen]
    refine sSup_le fun K hK => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact comp_commute_normal hY (hcp.comp K hK) (hcp.K_normal hK)
      (fun h => hY𝓛 (by rw [h]; exact hK)) y hy x hx
  apply qs_not_comm_subgroup hY.2.2
  intro y hy y' hy'
  exact Subgroup.mem_centralizer_iff.1 (hcen (hY.1 hy')) y hy

theorem isComponentOf_gLBConj_norm {L K : Subgroup G} {b : G}
    (hb : b ∈ Subgroup.normalizer (L : Set G)) (hK : CFSG.Open.IsComponentOf K L) :
    CFSG.Open.IsComponentOf (GLBConj b K) L := by
  have hbL : ∀ h, h ∈ L ↔ b * h * b⁻¹ ∈ L := fun h => (Subgroup.mem_normalizer_iff.1 hb h)
  set φ : G →* G := (MulAut.conj b⁻¹).toMonoidHom with hφ
  have hφapp : ∀ y, φ y = b⁻¹ * y * b := fun y => by simp [hφ]
  have hLφ : L.map φ = L := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hφapp]
      refine (hbL _).2 ?_
      have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
      rw [e]
      exact hy
    · intro hx
      refine ⟨b * x * b⁻¹, (hbL x).1 hx, ?_⟩
      rw [hφapp]
      group
  have hK' : CFSG.Open.IsComponentOf (K.map φ) (L.map φ) :=
    ⟨Subgroup.map_mono hK.1, CFSG.ComponentClassification.Components.chain_map φ hK.2.1,
      CFSG.ComponentClassification.Components.quasisimple_of_equiv
        (K.equivMapOfInjective φ (MulAut.conj b⁻¹).injective).symm hK.2.2⟩
  rw [hLφ] at hK'
  exact hK'

theorem CPData.conj_mem {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {b : G} (hb : b ∈ B) {K : Subgroup G} (hK : K ∈ 𝓛) :
    GLBConj b K ∈ 𝓛 :=
  hcp.comp_mem (isComponentOf_gLBConj_norm (hcp.norm hb) (hcp.comp K hK))

theorem gLBConj_card (b : G) (K : Subgroup G) : Nat.card (GLBConj b K) = Nat.card K := by
  unfold GLBConj
  exact Nat.card_congr (K.equivMapOfInjective (MulAut.conj b⁻¹).toMonoidHom
    (MulAut.conj b⁻¹).injective).symm

theorem CPData.p_dvd_card {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hp : p.Prime)
    (hcp : CPData p B L 𝓛) (hpL : p ∣ Nat.card L) {K : Subgroup G} (hK : K ∈ 𝓛) :
    p ∣ Nat.card K := by
  haveI : Fact p.Prime := ⟨hp⟩
  set O : Subgroup G := (CFSG.pPrimeCore p L).map L.subtype with hO
  have hOcop : Nat.Coprime p (Nat.card O) := by
    have : Nat.card O = Nat.card (CFSG.pPrimeCore p L) :=
      Nat.card_congr ((CFSG.pPrimeCore p L).equivMapOfInjective L.subtype L.subtype_injective).symm
    rw [this]
    exact CFSG.pPrimeCore_coprime_card
  have hex : ∃ K' ∈ 𝓛, ¬ K' ≤ O := by
    by_contra hall
    push_neg at hall
    have hLO : L ≤ O := by
      rw [hcp.gen]
      exact sSup_le hall
    have hdvd : Nat.card L ∣ Nat.card O := Subgroup.card_dvd_of_le hLO
    have : p ∣ Nat.card O := hpL.trans hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 hOcop this
  obtain ⟨K', hK'𝓛, hK'O⟩ := hex
  have hK'p : p ∣ Nat.card K' := by
    by_contra hnd
    apply hK'O
    have hcop : Nat.Coprime p (Nat.card (K'.subgroupOf L)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hcp.K_le_L hK'𝓛)).toEquiv]
      exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).symm
    have hmem : K'.subgroupOf L ≤ CFSG.pPrimeCore p L :=
      le_sSup ⟨hcp.K_normal hK'𝓛, hcop⟩
    intro k hk
    exact ⟨⟨k, hcp.K_le_L hK'𝓛 hk⟩, hmem (Subgroup.mem_subgroupOf.2 hk), rfl⟩
  obtain ⟨b, -, hb⟩ := hcp.trans K' hK'𝓛 K hK
  rw [← hb, gLBConj_card]
  exact hK'p

section Diagonal

variable {G : Type*} [Group G]

def cj (b k : G) (j : ℕ) : G := (b ^ j)⁻¹ * k * b ^ j

def dlProd (b k : G) (n : ℕ) : G := ((List.range n).map fun j => cj b k j).prod

theorem cj_succ (b k : G) (j : ℕ) : b⁻¹ * cj b k j * b = cj b k (j + 1) := by
  simp only [cj, pow_succ]
  group

theorem cj_mul (b k k' : G) (j : ℕ) : cj b (k * k') j = cj b k j * cj b k' j := by
  simp only [cj]
  group

theorem cj_zero (b k : G) : cj b k 0 = k := by
  simp only [cj, pow_zero, inv_one, one_mul, mul_one]

theorem dlProd_succ' (b k : G) (n : ℕ) :
    dlProd b k (n + 1) = k * ((List.range n).map fun j => cj b k (j + 1)).prod := by
  simp only [dlProd, List.range_succ_eq_map, List.map_cons, List.map_map, List.prod_cons, cj_zero]
  rfl

theorem list_prod_mul_interchange {M : Type*} [Monoid M] (f g : ℕ → M) (n : ℕ)
    (h : ∀ i j, i < n → j < n → i ≠ j → Commute (f i) (g j)) :
    ((List.range n).map f).prod * ((List.range n).map g).prod =
      ((List.range n).map fun j => f j * g j).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    have ih' := ih (fun i j hi hj hij => h i j (by omega) (by omega) hij)
    have hcomm : Commute (f n) ((List.map g (List.range n)).prod) := by
      apply Commute.list_prod_right
      intro y hy
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
      have hjn : j < n := List.mem_range.1 hj
      exact h n j (Nat.lt_succ_self n) (by omega) (by omega)
    simp only [List.range_succ, List.map_append, List.prod_append, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, mul_one] at ih' ⊢
    calc ((List.map f (List.range n)).prod * f n) * ((List.map g (List.range n)).prod * g n)
        = (List.map f (List.range n)).prod * (f n * (List.map g (List.range n)).prod) *
            g n := by simp only [mul_assoc]
      _ = (List.map f (List.range n)).prod * ((List.map g (List.range n)).prod * f n) *
            g n := by rw [hcomm.eq]
      _ = ((List.map f (List.range n)).prod * (List.map g (List.range n)).prod) * (f n * g n) := by
            simp only [mul_assoc]
      _ = _ := by rw [ih']

theorem dlProd_mul (b k k' : G) (n : ℕ)
    (h : ∀ i j, i < n → j < n → i ≠ j → Commute (cj b k i) (cj b k' j)) :
    dlProd b (k * k') n = dlProd b k n * dlProd b k' n := by
  simp only [dlProd, cj_mul]
  exact (list_prod_mul_interchange (fun j => cj b k j) (fun j => cj b k' j) n h).symm

theorem conj_dlProd (b k : G) (m : ℕ) (hb : b ^ (m + 1) = 1)
    (hk : ∀ j < m, Commute k (cj b k (j + 1))) :
    b⁻¹ * dlProd b k (m + 1) * b = dlProd b k (m + 1) := by
  have hk' : Commute k ((List.range m).map fun j => cj b k (j + 1)).prod := by
    apply Commute.list_prod_right
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact hk j (List.mem_range.1 hj)
  have hc : cj b k (m + 1) = k := by simp only [cj, hb, inv_one, one_mul, mul_one]
  have hconj : b⁻¹ * dlProd b k (m + 1) * b =
      ((List.range (m + 1)).map fun j => cj b k (j + 1)).prod := by
    have h1 : ∀ x : G, b⁻¹ * x * b = MulAut.conj b⁻¹ x := fun x => by
      simp [MulAut.conj_apply]
    rw [h1, dlProd, map_list_prod, List.map_map]
    congr 1
    apply List.map_congr_left
    intro j _
    simp only [Function.comp_apply]
    rw [MulAut.conj_apply, inv_inv]
    exact cj_succ b k j
  rw [hconj, dlProd_succ', List.range_succ, List.map_append, List.prod_append, List.map_cons,
    List.map_nil, List.prod_cons, List.prod_nil, mul_one, hc]
  exact (hk'.eq).symm

def Rprod (m : ℕ) (b k : G) : G := ((List.range m).map fun j => cj b k (j + 2)).prod

theorem dlProd_split (b k : G) (m : ℕ) : dlProd b k (m + 2) = k * (cj b k 1 * Rprod m b k) := by
  unfold Rprod
  rw [show m + 2 = (m + 1) + 1 from rfl, dlProd_succ', List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.prod_cons, Function.comp_def]

end Diagonal

section Orbits

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB

variable {G : Type*} [Group G] [Finite G]

def NN (𝓛 : Set (Subgroup G)) (K : Subgroup G) : Subgroup G :=
  sSup {X | X ∈ 𝓛 ∧ X ≠ K}

theorem NN_le_centralizer {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K : Subgroup G} (hK : K ∈ 𝓛) :
    NN 𝓛 K ≤ Subgroup.centralizer (K : Set G) := by
  refine sSup_le fun X hX => ?_
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact hcp.comm K hK X hX.1 (Ne.symm hX.2) h hh x hx

theorem mem_sup_of_comm {K N : Subgroup G} (hc : ∀ n ∈ N, ∀ x ∈ K, n * x = x * n) {y : G}
    (hy : y ∈ K ⊔ N) : ∃ k ∈ K, ∃ n ∈ N, y = k * n := by
  let P : Subgroup G :=
    { carrier := {y | ∃ k ∈ K, ∃ n ∈ N, y = k * n}
      one_mem' := ⟨1, K.one_mem, 1, N.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨k1, hk1, n1, hn1, rfl⟩ ⟨k2, hk2, n2, hn2, rfl⟩
        refine ⟨k1 * k2, K.mul_mem hk1 hk2, n1 * n2, N.mul_mem hn1 hn2, ?_⟩
        have := hc n1 hn1 k2 hk2
        calc k1 * n1 * (k2 * n2) = k1 * (n1 * k2) * n2 := by group
          _ = k1 * k2 * (n1 * n2) := by rw [this]; group
      inv_mem' := by
        rintro _ ⟨k1, hk1, n1, hn1, rfl⟩
        have hcm : Commute k1 n1 := (hc n1 hn1 k1 hk1).symm
        refine ⟨k1⁻¹, K.inv_mem hk1, n1⁻¹, N.inv_mem hn1, ?_⟩
        rw [mul_inv_rev]
        exact (hcm.inv_inv).eq.symm }
  have hKP : K ≤ P := fun x hx => ⟨x, hx, 1, N.one_mem, by simp⟩
  have hNP : N ≤ P := fun x hx => ⟨1, K.one_mem, x, hx, by simp⟩
  have hsup : K ⊔ N ≤ P := sup_le hKP hNP
  exact hsup hy

theorem NN_conj_le {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {g : G} (hg : g ∈ B) {K : Subgroup G} (hK : K ∈ 𝓛) :
    GLBConj g (NN 𝓛 K) ≤ NN 𝓛 (GLBConj g K) := by
  have key : ∀ X ∈ {X | X ∈ 𝓛 ∧ X ≠ K}, GLBConj g X ≤ NN 𝓛 (GLBConj g K) := by
    intro X hX
    have e1 : ∀ Y : Subgroup G, GLBConj g⁻¹ (GLBConj g Y) = Y := fun Y => by
      simpa using gLBConj_gLBConj_inv g⁻¹ Y
    refine le_sSup ⟨hcp.conj_mem hg hX.1, fun h => hX.2 ?_⟩
    calc X = GLBConj g⁻¹ (GLBConj g X) := (e1 X).symm
      _ = GLBConj g⁻¹ (GLBConj g K) := by rw [h]
      _ = K := e1 K
  unfold NN GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun X hX => ?_
  exact (Subgroup.map_le_iff_le_comap).1 (key X hX)

theorem gLBConj_eq_norm (K : Subgroup G) {g h : G} (hgh : GLBConj g K = GLBConj h K) :
    h * g⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
  have key : ∀ g h : G, GLBConj g K = GLBConj h K → ∀ x ∈ K, (h * g⁻¹) * x * (h * g⁻¹)⁻¹ ∈ K := by
    intro g h hgh x hx
    have hx' : g⁻¹ * x * g ∈ GLBConj g K :=
      mem_gLBConj.2 (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
    rw [hgh] at hx'
    have := mem_gLBConj.1 hx'
    convert this using 1 <;> group
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact key g h hgh x
  · intro hx
    have := key h g hgh.symm _ hx
    convert this using 1 <;> group

theorem mem_of_pow_mem_normalizer {p : ℕ} (hp : p.Prime) {G : Type*} [Group G] {b : G}
    (hbp : b ^ p = 1) {N : Subgroup G} {d : ℕ} (hd0 : 0 < d) (hdp : d < p) (h : b ^ d ∈ N) :
    b ∈ N := by
  have hcop : Nat.Coprime d p := by
    have hndvd : ¬ p ∣ d := fun hd => absurd (Nat.le_of_dvd hd0 hd) (by omega)
    exact ((Nat.Prime.coprime_iff_not_dvd hp).2 hndvd).symm
  have hg := Nat.gcd_eq_gcd_ab d p
  rw [hcop.gcd_eq_one] at hg
  have hg' : (1 : ℤ) = (d : ℤ) * Nat.gcdA d p + (p : ℤ) * Nat.gcdB d p := by
    exact_mod_cast hg
  have e : b ^ (1 : ℤ) = b ^ ((d : ℤ) * Nat.gcdA d p + (p : ℤ) * Nat.gcdB d p) := by
    rw [← hg']
  rw [zpow_one, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hbp, one_zpow,
    mul_one] at e
  rw [e]
  exact N.zpow_mem h _

section DiagSub

variable {G : Type*} [Group G] [Finite G]

theorem orb_ne {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} {b : G} (hbp : b ^ p = 1)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {i j : ℕ} (hi : i < p) (hj : j < p)
    (hij : i ≠ j) : GLBConj (b ^ i) K₀ ≠ GLBConj (b ^ j) K₀ := by
  intro heq
  have hu := gLBConj_eq_norm K₀ heq
  rcases Nat.lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨d, rfl⟩ : ∃ d, j = i + d := ⟨j - i, by omega⟩
    have hd : b ^ (i + d) * (b ^ i)⁻¹ = b ^ d := by rw [pow_add]; group
    rw [hd] at hu
    exact hbN (mem_of_pow_mem_normalizer hp hbp (by omega) (by omega) hu)
  · obtain ⟨d, rfl⟩ : ∃ d, i = j + d := ⟨i - j, by omega⟩
    have hd : (b ^ j * (b ^ (j + d))⁻¹)⁻¹ = b ^ d := by rw [pow_add]; group
    have hu' := (Subgroup.normalizer (K₀ : Set G)).inv_mem hu
    rw [hd] at hu'
    exact hbN (mem_of_pow_mem_normalizer hp hbp (by omega) (by omega) hu')

theorem cj_mem_Kj {K₀ : Subgroup G} {b k : G} (hk : k ∈ K₀) (j : ℕ) :
    cj b k j ∈ GLBConj (b ^ j) K₀ := by
  rw [mem_gLBConj]
  unfold cj
  rw [show b ^ j * ((b ^ j)⁻¹ * k * b ^ j) * (b ^ j)⁻¹ = k by group]
  exact hk

theorem cj_comm {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {x y : G} (hx : x ∈ K₀) (hy : y ∈ K₀)
    {i j : ℕ} (hi : i < p) (hj : j < p) (hij : i ≠ j) :
    Commute (cj b x i) (cj b y j) := by
  have hbp : b ^ p = 1 := hcp.elem.2 b hb
  have hKi : GLBConj (b ^ i) K₀ ∈ 𝓛 := hcp.conj_mem (B.pow_mem hb i) hK₀
  have hKj : GLBConj (b ^ j) K₀ ∈ 𝓛 := hcp.conj_mem (B.pow_mem hb j) hK₀
  exact hcp.comm _ hKi _ hKj (orb_ne hp hcp hbp hbN hi hj hij) _ (cj_mem_Kj hx i) _
    (cj_mem_Kj hy j)

def Aset (p : ℕ) (b : G) (K₀ : Subgroup G) : Set (Subgroup G) :=
  {X | ∃ j : ℕ, 1 ≤ j ∧ j < p ∧ X = GLBConj (b ^ j) K₀}

def Asub (p : ℕ) (b : G) (K₀ : Subgroup G) : Subgroup G := sSup (Aset p b K₀)

theorem Asub_le_NN {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    Asub p b K₀ ≤ NN 𝓛 K₀ := by
  have hbp : b ^ p = 1 := hcp.elem.2 b hb
  refine sSup_le fun X hX => ?_
  obtain ⟨j, hj1, hjp, rfl⟩ := hX
  refine le_sSup ⟨hcp.conj_mem (B.pow_mem hb j) hK₀, fun h => ?_⟩
  have h0 : GLBConj (b ^ 0) K₀ = K₀ := by simp [gLBConj_one]
  exact orb_ne hp hcp hbp hbN (i := 0) (j := j) hp.pos hjp (by omega) (by rw [h0, h])

theorem Asub_le_centralizer {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    Asub p b K₀ ≤ Subgroup.centralizer (K₀ : Set G) :=
  le_trans (Asub_le_NN hp hcp hK₀ hb hbN) (NN_le_centralizer hcp hK₀)

theorem cj_mem_Asub {p : ℕ} {K₀ : Subgroup G} {b k : G} (hk : k ∈ K₀) {j : ℕ} (hj1 : 1 ≤ j)
    (hjp : j < p) : cj b k j ∈ Asub p b K₀ :=
  (le_sSup ⟨j, hj1, hjp, rfl⟩ : GLBConj (b ^ j) K₀ ≤ Asub p b K₀) (cj_mem_Kj hk j)

theorem cj_mem_L {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B) {k : G} (hk : k ∈ K₀) (j : ℕ) :
    cj b k j ∈ L :=
  (hcp.K_le_L (hcp.conj_mem (B.pow_mem hb j) hK₀)) (cj_mem_Kj hk j)

def dlHom {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) : K₀ →* G :=
  MonoidHom.mk' (fun k : K₀ => dlProd b (k : G) p) (fun x y => by
    simp only [Subgroup.coe_mul]
    exact dlProd_mul b x y p (fun i j hi hj hij => cj_comm hp hcp hK₀ hb hbN x.2 y.2 hi hj hij))

theorem dlHom_apply {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) (k : K₀) :
    dlHom hp hcp hK₀ hb hbN k = dlProd b (k : G) p := by
  simp only [dlHom, MonoidHom.mk'_apply]

theorem dlProd_mem_L {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B) {k : G} (hk : k ∈ K₀) :
    dlProd b k p ∈ L := by
  unfold dlProd
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact cj_mem_L hcp hK₀ hb hk j

theorem dlProd_eq_k_mul {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {k : G} (hk : k ∈ K₀) :
    dlProd b k p = k * ((List.range (p - 1)).map fun j => cj b k (j + 1)).prod ∧
      ((List.range (p - 1)).map fun j => cj b k (j + 1)).prod ∈ Asub p b K₀ := by
  have hp1 : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp.pos).symm
  constructor
  · conv_lhs => rw [hp1]
    rw [dlProd_succ']
  · apply Subgroup.list_prod_mem
    intro x hx
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
    have hj' : j < p - 1 := List.mem_range.1 hj
    exact cj_mem_Asub hk (by omega) (by omega)

theorem dlProd_comm_b {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {k : G} (hk : k ∈ K₀) :
    dlProd b k p ∈ Subgroup.centralizer ({b} : Set G) := by
  have hbp : b ^ p = 1 := hcp.elem.2 b hb
  obtain ⟨m, hm⟩ : ∃ m, p = m + 1 := ⟨p - 1, by have := hp.pos; omega⟩
  have hbm : b ^ (m + 1) = 1 := hm ▸ hbp
  have hk' : ∀ j < m, Commute k (cj b k (j + 1)) := by
    intro j _
    have := cj_comm hp hcp hK₀ hb hbN hk hk (i := 0) (j := j + 1) hp.pos
      (by omega) (by omega)
    rw [cj_zero] at this
    exact this
  have hconj := conj_dlProd b k m hbm hk'
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hm' : dlProd b k p = dlProd b k (m + 1) := by rw [hm]
  rw [hm']
  calc dlProd b k (m + 1) * b = b * (b⁻¹ * dlProd b k (m + 1) * b) := by group
    _ = b * dlProd b k (m + 1) := by rw [hconj]

theorem dlHom_ker_le_center {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    (dlHom hp hcp hK₀ hb hbN).ker ≤ Subgroup.center K₀ := by
  intro k hk
  rw [MonoidHom.mem_ker, dlHom_apply] at hk
  obtain ⟨hk1, hP⟩ := dlProd_eq_k_mul hp hcp hK₀ hb hbN k.2
  rw [hk1] at hk
  set P := ((List.range (p - 1)).map fun j => cj b k (j + 1)).prod with hPdef
  have hPc : P ∈ Subgroup.centralizer (K₀ : Set G) := Asub_le_centralizer hp hcp hK₀ hb hbN hP
  have hkP : (k : G) = P⁻¹ := eq_inv_of_mul_eq_one_left hk
  rw [Subgroup.mem_center_iff]
  intro g
  have hcg : Commute (g : G) P := (Subgroup.mem_centralizer_iff.1 hPc) g g.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  rw [hkP]
  exact (hcg.inv_right).eq

theorem dlHom_range_le {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    (dlHom hp hcp hK₀ hb hbN).range ≤ L ⊓ Subgroup.centralizer ({b} : Set G) := by
  rintro _ ⟨k, rfl⟩
  rw [dlHom_apply]
  exact ⟨dlProd_mem_L hcp hK₀ hb k.2, dlProd_comm_b hp hcp hK₀ hb hbN k.2⟩

theorem dlHom_range_pdvd {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) (hpK : p ∣ Nat.card K₀) :
    p ∣ Nat.card (dlHom hp hcp hK₀ hb hbN).range := by
  have hq : CFSG.Open.IsQuasisimple K₀ := (hcp.comp K₀ hK₀).2.2
  obtain ⟨x, hxc, n, hn⟩ := exists_noncentral_pElt hp hq hpK
  set D := (dlHom hp hcp hK₀ hb hbN).range with hD
  have hyD : (dlHom hp hcp hK₀ hb hbN x) ∈ D := MonoidHom.mem_range.2 ⟨x, rfl⟩
  set z : D := ⟨_, hyD⟩ with hz
  have hz_pow : z ^ (p ^ n) = 1 := by
    apply Subtype.ext
    simp only [hz, Subgroup.coe_pow, Subgroup.coe_one, map_pow]
    rw [← map_pow, hn, map_one]
  have hz_ne : z ≠ 1 := by
    intro h1
    apply hxc
    apply dlHom_ker_le_center hp hcp hK₀ hb hbN
    rw [MonoidHom.mem_ker]
    have := congrArg Subtype.val h1
    simpa [hz] using this
  have hord : orderOf z ∣ p ^ n := orderOf_dvd_of_pow_eq_one hz_pow
  obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow hp).1 hord
  have hi0 : i ≠ 0 := by
    rintro rfl
    apply hz_ne
    rw [pow_zero] at hi'
    exact orderOf_eq_one_iff.1 hi'
  have hpz : p ∣ orderOf z := by
    rw [hi']
    exact dvd_pow_self p hi0
  exact hpz.trans (orderOf_dvd_natCard z)

theorem L_le_sup_NN {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) :
    L ≤ K₀ ⊔ NN 𝓛 K₀ := by
  rw [hcp.gen]
  refine sSup_le fun X hX => ?_
  by_cases hXK : X = K₀
  · subst hXK
    exact le_sup_left
  · exact le_sup_of_le_right (le_sSup ⟨hX, hXK⟩)

theorem dlHom_normal {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    ((dlHom hp hcp hK₀ hb hbN).range.subgroupOf (L ⊓ Subgroup.centralizer ({b} : Set G))).Normal := by
  have hbp : b ^ p = 1 := hcp.elem.2 b hb
  set D := (dlHom hp hcp hK₀ hb hbN).range with hD
  have hxcomm_all : ∀ n' : G, (∀ j < p, ∀ y ∈ GLBConj (b ^ j) K₀, Commute n' y) →
      ∀ x ∈ D, Commute n' x := by
    intro n' hK x hx
    obtain ⟨k, rfl⟩ := MonoidHom.mem_range.1 hx
    rw [dlHom_apply]
    unfold dlProd
    apply Commute.list_prod_right
    intro y hy
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hy
    exact hK j (List.mem_range.1 hj) _ (cj_mem_Kj k.2 j)
  have hconj : ∀ c ∈ L ⊓ Subgroup.centralizer ({b} : Set G), ∀ x ∈ D, c * x * c⁻¹ ∈ D := by
    rintro c ⟨hcL, hcb⟩ x hx
    have hcb' : Commute c b := Subgroup.mem_centralizer_singleton_iff.1 hcb
    obtain ⟨k₀, hk₀, n, hn, hcn⟩ := mem_sup_of_comm
      (fun n hn x hx => ((Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hK₀ hn)) x hx).symm)
      (L_le_sup_NN hcp hK₀ hcL)
    obtain ⟨hd1, hP⟩ := dlProd_eq_k_mul hp hcp hK₀ hb hbN hk₀
    set P := ((List.range (p - 1)).map fun j => cj b k₀ (j + 1)).prod with hPdef
    have hPN : P ∈ NN 𝓛 K₀ := Asub_le_NN hp hcp hK₀ hb hbN hP
    set d := dlProd b (k₀ : G) p with hddef
    have hdD : d ∈ D := MonoidHom.mem_range.2 ⟨⟨k₀, hk₀⟩, rfl⟩
    have hdb : Commute d b := Subgroup.mem_centralizer_singleton_iff.1
      (dlProd_comm_b hp hcp hK₀ hb hbN hk₀)
    set n' := P⁻¹ * n with hn'
    have hn'NN : n' ∈ NN 𝓛 K₀ := (NN 𝓛 K₀).mul_mem ((NN 𝓛 K₀).inv_mem hPN) hn
    have hcn' : n' = d⁻¹ * c := by
      rw [hn', hcn, hd1]
      group
    have hcomm_n' : Commute n' b := by
      rw [hcn']
      exact (hdb.inv_left).mul_left hcb'
    have hK_comm : ∀ j < p, ∀ y ∈ GLBConj (b ^ j) K₀, Commute n' y := by
      intro j hj y hy
      have hcg : Commute n' (b ^ j) := hcomm_n'.pow_right j
      have hgn : (b ^ j) * n' * (b ^ j)⁻¹ = n' := by
        rw [← hcg.eq]
        group
      have hmem : n' ∈ GLBConj (b ^ j) (NN 𝓛 K₀) := mem_gLBConj.2 (by rw [hgn]; exact hn'NN)
      have hKj : GLBConj (b ^ j) K₀ ∈ 𝓛 := hcp.conj_mem (B.pow_mem hb j) hK₀
      have hmemN : n' ∈ NN 𝓛 (GLBConj (b ^ j) K₀) := NN_conj_le hcp (B.pow_mem hb j) hK₀ hmem
      exact ((Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hKj hmemN)) y hy).symm
    have hxc := hxcomm_all n' hK_comm x hx
    have hfin : c * x * c⁻¹ = d * x * d⁻¹ := by
      have hc : c = d * n' := by rw [hcn']; group
      rw [hc]
      calc d * n' * x * (d * n')⁻¹ = d * (n' * x * n'⁻¹) * d⁻¹ := by group
        _ = d * x * d⁻¹ := by rw [hxc.eq]; group
    rw [hfin]
    exact D.mul_mem (D.mul_mem hdD hx) (D.inv_mem hdD)
  constructor
  intro n hn g
  rw [Subgroup.mem_subgroupOf] at hn ⊢
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  exact hconj g.1 g.2 n.1 hn

theorem dlHom_range_quasisimple {p : ℕ} (hp : p.Prime) {B L : Subgroup G}
    {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G}
    (hb : b ∈ B) (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) :
    CFSG.Open.IsQuasisimple (dlHom hp hcp hK₀ hb hbN).range := by
  have hqK : CFSG.Open.IsQuasisimple (K₀ ⧸ (dlHom hp hcp hK₀ hb hbN).ker) :=
    CFSG.ComponentClassification.Quasisimple.central_quotient (hcp.comp K₀ hK₀).2.2 _
      (dlHom_ker_le_center hp hcp hK₀ hb hbN)
  exact CFSG.ComponentClassification.Components.quasisimple_of_equiv
    (QuotientGroup.quotientKerEquivRange _).symm hqK

theorem dlHom_le_layer {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) (hpK : p ∣ Nat.card K₀) :
    (dlHom hp hcp hK₀ hb hbN).range ≤ GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set G)) := by
  have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp
    (dlHom_range_quasisimple hp hcp hK₀ hb hbN) (dlHom_range_pdvd hp hcp hK₀ hb hbN hpK)
    (dlHom_range_le hp hcp hK₀ hb hbN) (dlHom_normal hp hcp hK₀ hb hbN)
  unfold GLAPLayer
  exact le_sSup hcomp

def layerSet (p : ℕ) (B L K₀ : Subgroup G) : Set (Subgroup G) :=
  {Z | ∃ b ∈ B, b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set G) ∨
    b ∉ Subgroup.normalizer (K₀ : Set G)) ∧ Z = GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set G))}

theorem dl_le_W {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) (hpK : p ∣ Nat.card K₀) :
    (dlHom hp hcp hK₀ hb hbN).range ≤ sSup (layerSet p B L K₀) := by
  refine le_trans (dlHom_le_layer hp hcp hK₀ hb hbN hpK) (le_sSup ?_)
  exact ⟨b, hb, fun h => hbN (h ▸ Subgroup.one_mem _), Or.inr hbN, rfl⟩

theorem commute_sSup {S T : Set (Subgroup G)}
    (h : ∀ X ∈ S, ∀ Y ∈ T, ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    ∀ x ∈ sSup S, ∀ y ∈ sSup T, x * y = y * x := by
  have h1 : ∀ Y ∈ T, ∀ y ∈ Y, sSup S ≤ Subgroup.centralizer ({y} : Set G) := by
    intro Y hY y hy
    refine sSup_le fun X hX => ?_
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact h X hX Y hY x hx y hy
  have h2 : sSup T ≤ Subgroup.centralizer ((sSup S : Subgroup G) : Set G) := by
    refine sSup_le fun Y hY => ?_
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.1 (h1 Y hY y hy hx)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.1 (h2 hy) x hx)

theorem Aset_commute {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b b' : G} (hb : b ∈ B)
    (hb' : b' ∈ B) (hindep : ∀ i j : ℕ, GLBConj (b ^ i) K₀ = GLBConj (b' ^ j) K₀ → p ∣ i) :
    ∀ x ∈ Asub p b K₀, ∀ y ∈ Asub p b' K₀, x * y = y * x := by
  apply commute_sSup
  rintro X ⟨i, hi1, hip, rfl⟩ Y ⟨j, hj1, hjp, rfl⟩ x hx y hy
  have hne : GLBConj (b ^ i) K₀ ≠ GLBConj (b' ^ j) K₀ := by
    intro h
    have hd := hindep i j h
    have := Nat.le_of_dvd (by omega) hd
    omega
  exact hcp.comm _ (hcp.conj_mem (B.pow_mem hb i) hK₀) _ (hcp.conj_mem (B.pow_mem hb' j) hK₀)
    hne x hx y hy

theorem R2_K₀_le {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b b' : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) (hb' : b' ∈ B)
    (hb'N : b' ∉ Subgroup.normalizer (K₀ : Set G))
    (hindep : ∀ i j : ℕ, GLBConj (b ^ i) K₀ = GLBConj (b' ^ j) K₀ → p ∣ i)
    (hpK : p ∣ Nat.card K₀) : K₀ ≤ sSup (layerSet p B L K₀) := by
  set W := sSup (layerSet p B L K₀) with hW
  have hdW : ∀ c ∈ B, c ∉ Subgroup.normalizer (K₀ : Set G) →
      ∀ k ∈ K₀, dlProd c k p ∈ W := by
    intro c hc hcN k hk
    have := dl_le_W hp hcp hK₀ hc hcN hpK (MonoidHom.mem_range.2 ⟨⟨k, hk⟩, rfl⟩)
    rwa [dlHom_apply] at this
  have key : ∀ k ∈ K₀, ∀ k' ∈ K₀, ⁅k, k'⁆ ∈ W := by
    intro k hk k' hk'
    obtain ⟨hu1, hr⟩ := dlProd_eq_k_mul hp hcp hK₀ hb hbN hk
    obtain ⟨hu1', hr'⟩ := dlProd_eq_k_mul hp hcp hK₀ hb' hb'N hk'
    set r := ((List.range (p - 1)).map fun j => cj b k (j + 1)).prod with hrdef
    set r' := ((List.range (p - 1)).map fun j => cj b' k' (j + 1)).prod with hr'def
    have hrk' : r * k' = k' * r :=
      ((Subgroup.mem_centralizer_iff.1 (Asub_le_centralizer hp hcp hK₀ hb hbN hr)) k' hk').symm
    have hr'k : r' * k = k * r' :=
      ((Subgroup.mem_centralizer_iff.1 (Asub_le_centralizer hp hcp hK₀ hb' hb'N hr')) k hk).symm
    have hrr' : r * r' = r' * r := Aset_commute hp hcp hK₀ hb hb' hindep r hr r' hr'
    have hu : dlProd b k p = k * r := hu1
    have hu' : dlProd b' k' p = k' * r' := hu1'
    have hmemu : dlProd b k p ∈ W := hdW b hb hbN k hk
    have hmemu' : dlProd b' k' p ∈ W := hdW b' hb' hb'N k' hk'
    have e1 : (k * r) * (k' * r') = k * k' * (r * r') := by
      calc k * r * (k' * r') = k * (r * k') * r' := by group
        _ = k * (k' * r) * r' := by rw [hrk']
        _ = k * k' * (r * r') := by group
    have e2 : (k' * r') * (k * r) = k' * k * (r * r') := by
      calc k' * r' * (k * r) = k' * (r' * k) * r := by group
        _ = k' * (k * r') * r := by rw [hr'k]
        _ = k' * k * (r' * r) := by group
        _ = k' * k * (r * r') := by rw [hrr']
    have hcomm_eq : ⁅dlProd b k p, dlProd b' k' p⁆ = ⁅k, k'⁆ := by
      rw [hu, hu']
      calc ⁅k * r, k' * r'⁆ = (k * r) * (k' * r') * ((k' * r') * (k * r))⁻¹ := by
            rw [commutatorElement_def]; group
        _ = (k * k' * (r * r')) * (k' * k * (r * r'))⁻¹ := by rw [e1, e2]
        _ = ⁅k, k'⁆ := by rw [commutatorElement_def]; group
    rw [← hcomm_eq]
    rw [commutatorElement_def]
    exact W.mul_mem (W.mul_mem (W.mul_mem hmemu hmemu') (W.inv_mem hmemu)) (W.inv_mem hmemu')
  have hcomm_le : ⁅(⊤ : Subgroup K₀), (⊤ : Subgroup K₀)⁆ ≤ W.comap K₀.subtype := by
    refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact key _ a.2 _ b.2
  have htop : (⊤ : Subgroup K₀) ≤ W.comap K₀.subtype := by
    have hq := (hcp.comp K₀ hK₀).2.2
    rw [← hq.1, commutator_def]
    exact hcomm_le
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : K₀))

theorem layer_gLBConj_le {p : ℕ} (X : Subgroup G) (g : G) :
    GLBConj g (GLAPLayer p X) ≤ GLAPLayer p (GLBConj g X) := by
  unfold GLAPLayer
  unfold GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun K hK => ?_
  exact (Subgroup.map_le_iff_le_comap).1 (le_sSup (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_gLBConj hK g))

theorem conj_comm_aux {g y x : G} (hgy : g * y = y * g) (hx : x * y = y * x) :
    (g * x * g⁻¹) * y = y * (g * x * g⁻¹) := by
  have hy' : g⁻¹ * y = y * g⁻¹ := by
    calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hgy]
      _ = y * g⁻¹ := by group
  calc g * x * g⁻¹ * y = g * x * (g⁻¹ * y) := by group
    _ = g * x * (y * g⁻¹) := by rw [hy']
    _ = g * (x * y) * g⁻¹ := by group
    _ = g * (y * x) * g⁻¹ := by rw [hx]
    _ = g * y * x * g⁻¹ := by group
    _ = y * g * x * g⁻¹ := by rw [hgy]
    _ = y * (g * x * g⁻¹) := by group

theorem gLBConj_inf_centralizer {B L : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G))
    (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) {g y : G} (hg : g ∈ B) (hy : y ∈ B) :
    GLBConj g (L ⊓ Subgroup.centralizer ({y} : Set G)) = L ⊓ Subgroup.centralizer ({y} : Set G) := by
  have hgL : ∀ h, h ∈ L ↔ g * h * g⁻¹ ∈ L := fun h => Subgroup.mem_normalizer_iff.1 (hBN hg) h
  have hgy : g * y = y * g := hcomm g hg y hy
  have hgy' : g⁻¹ * y = y * g⁻¹ := by
    calc g⁻¹ * y = g⁻¹ * (y * g) * g⁻¹ := by group
      _ = g⁻¹ * (g * y) * g⁻¹ := by rw [hgy]
      _ = y * g⁻¹ := by group
  ext x
  rw [mem_gLBConj, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hgL x).2 h1, ?_⟩
    have h3 := conj_comm_aux hgy' h2
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e] at h3
    exact h3
  · rintro ⟨h1, h2⟩
    exact ⟨(hgL x).1 h1, conj_comm_aux hgy h2⟩

theorem zpow_gen_of_coprime {G : Type*} [Group G] {c : G} {p : ℕ} (hcp : c ^ p = 1) {d : ℕ}
    (hcop : Nat.Coprime d p) : ∃ A : ℤ, (c ^ d) ^ A = c := by
  have hg := Nat.gcd_eq_gcd_ab d p
  rw [hcop.gcd_eq_one] at hg
  have hg' : (1 : ℤ) = (d : ℤ) * Nat.gcdA d p + (p : ℤ) * Nat.gcdB d p := by
    exact_mod_cast hg
  refine ⟨Nat.gcdA d p, ?_⟩
  have e : c ^ (1 : ℤ) = c ^ ((d : ℤ) * Nat.gcdA d p + (p : ℤ) * Nat.gcdB d p) := by
    rw [← hg']
  rw [zpow_one, zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hcp,
    one_zpow, mul_one] at e
  exact e.symm

theorem mem_of_pow_coprime {G : Type*} [Group G] {c : G} {p : ℕ} (hcp : c ^ p = 1)
    {N : Subgroup G} {d : ℕ} (hcop : Nat.Coprime d p) (h : c ^ d ∈ N) : c ∈ N := by
  obtain ⟨A, hA⟩ := zpow_gen_of_coprime hcp hcop
  rw [← hA]
  exact N.zpow_mem h A

end DiagSub

section Main

variable {G : Type*} [Group G] [Finite G]

def Wof (p : ℕ) (B L K₀ : Subgroup G) : Subgroup G := sSup (layerSet p B L K₀)

theorem Wof_conj_le {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} {g : G} (hg : g ∈ B) :
    GLBConj g (Wof p B L K₀) ≤ Wof p B L K₀ := by
  have hcommB : ∀ x ∈ B, ∀ z ∈ B, x * z = z * x := fun x hx z hz => by
    have := hcp.elem.1.is_comm.comm ⟨x, hx⟩ ⟨z, hz⟩
    exact congrArg Subtype.val this
  unfold Wof GLBConj
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun Z hZ => ?_
  obtain ⟨y, hy, hy1, hyN, rfl⟩ := hZ
  have e := gLBConj_inf_centralizer hcp.norm hcommB hg hy
  have h1 := layer_gLBConj_le (p := p) (L ⊓ Subgroup.centralizer ({y} : Set G)) g
  rw [e] at h1
  exact (Subgroup.map_le_iff_le_comap).1 (h1.trans (le_sSup ⟨y, hy, hy1, hyN, rfl⟩))

theorem L_le_Wof_of_K₀_le {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hK : K₀ ≤ Wof p B L K₀) :
    L ≤ Wof p B L K₀ := by
  refine (le_of_eq hcp.gen).trans (sSup_le fun K hK' => ?_)
  obtain ⟨x, hx, hxK⟩ := hcp.trans K₀ hK₀ K hK'
  rw [← hxK]
  exact (gLBConj_mono x hK).trans (Wof_conj_le (K₀ := K₀) hcp hx)

theorem caseA_le {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hpL : p ∣ Nat.card L) {b : G} (hb : b ∈ B)
    (hb1 : b ≠ 1) (hbC : b ∈ Subgroup.centralizer (L : Set G)) : L ≤ Wof p B L K₀ := by
  have hLC : L ⊓ Subgroup.centralizer ({b} : Set G) = L := by
    ext x
    constructor
    · exact fun h => h.1
    · intro hx
      refine ⟨hx, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.2 ((Subgroup.mem_centralizer_iff.1 hbC) x hx)
  have hGL : L ≤ GLAPLayer p L := by
    refine (le_of_eq hcp.gen).trans (sSup_le fun K hK => ?_)
    have hcomp := CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal hp
      (hcp.comp K hK).2.2 (hcp.p_dvd_card hp hpL hK) (hcp.K_le_L hK) (hcp.K_normal hK)
    exact le_sSup (show K ∈ {X | GLAPComponent p L X} from hcomp)
  have hW : GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set G)) ≤ Wof p B L K₀ :=
    le_sSup ⟨b, hb, hb1, Or.inl hbC, rfl⟩
  rw [hLC] at hW
  exact hGL.trans hW

end Main

end Orbits

end CentralProduct

section Core

open CFSG.Open

variable {G : Type*} [Group G] [Finite G]

theorem exists_nontriv_N {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {L₁ : Subgroup G} {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀1 : b₀ ≠ 1)
    (hR1 : ∀ b' ∈ B, ∃ e : ℤ, b' * (b₀ ^ e)⁻¹ ∈ Subgroup.normalizer (L₁ : Set G))
    (hrank : p ^ 2 ≤ Nat.card B) :
    ∃ x ∈ B, x ∈ Subgroup.normalizer (L₁ : Set G) ∧ x ≠ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hcon
  push_neg at hcon
  have hBle : B ≤ Subgroup.zpowers b₀ := by
    intro b' hb'
    obtain ⟨e, he⟩ := hR1 b' hb'
    have hu : b' * (b₀ ^ e)⁻¹ ∈ B := B.mul_mem hb' (B.inv_mem (B.zpow_mem hb₀ e))
    have h1 := hcon _ hu he
    rw [mul_inv_eq_one] at h1
    exact Subgroup.mem_zpowers_iff.2 ⟨e, h1.symm⟩
  have hcard : Nat.card B ≤ Nat.card (Subgroup.zpowers b₀) := Subgroup.card_le_of_le hBle
  rw [Nat.card_zpowers] at hcard
  have hord : orderOf b₀ = p := orderOf_eq_prime (hcp.elem.2 b₀ hb₀) hb₀1
  rw [hord] at hcard
  have := hp.two_le
  nlinarith

def Zl (L : Subgroup G) : Subgroup G := L ⊓ Subgroup.centralizer (L : Set G)

def MK (𝓛 : Set (Subgroup G)) (L M : Subgroup G) : Subgroup G := Zl L ⊔ NN 𝓛 M

theorem NN_le_L {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    (M : Subgroup G) : NN 𝓛 M ≤ L :=
  sSup_le fun X hX => (hcp.comp X hX.1).1

theorem Zl_comm_left {L : Subgroup G} {z : G} (hz : z ∈ Zl L) {x : G} (hx : x ∈ L) :
    z * x = x * z :=
  ((Subgroup.mem_centralizer_iff.1 hz.2) x hx).symm

theorem L_le_normalizer_NN {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) :
    L ≤ Subgroup.normalizer (NN 𝓛 M : Set G) := by
  refine (le_of_eq hcp.gen).trans (sSup_le fun X hX => ?_)
  by_cases hXM : X = M
  · subst hXM
    intro x hx
    refine normalizer_of_comm (NN 𝓛 X) x (fun h hh => ?_)
    exact (Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM hh)) x hx
  · exact (le_sSup ⟨hX, hXM⟩ : X ≤ NN 𝓛 M).trans Subgroup.le_normalizer

theorem MK_normal_L {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) {x : G} (hx : x ∈ L) {m : G}
    (hm : m ∈ MK 𝓛 L M) : x * m * x⁻¹ ∈ MK 𝓛 L M := by
  obtain ⟨z, hz, n, hn, rfl⟩ := mem_sup_of_comm
    (fun n hn z hz => (Zl_comm_left hz (hcp.K_le_L hM |> fun _ => (NN_le_L hcp M) hn)).symm)
    hm
  have hxn : x * n * x⁻¹ ∈ NN 𝓛 M := (Subgroup.mem_normalizer_iff.1 (L_le_normalizer_NN hcp hM hx) n).1 hn
  have hxz : x * z * x⁻¹ = z := by
    rw [← Zl_comm_left hz hx]
    group
  have : x * (z * n) * x⁻¹ = z * (x * n * x⁻¹) := by
    calc x * (z * n) * x⁻¹ = (x * z * x⁻¹) * (x * n * x⁻¹) := by group
      _ = z * (x * n * x⁻¹) := by rw [hxz]
  rw [this]
  exact (MK 𝓛 L M).mul_mem (le_sup_left (a := Zl L) (b := NN 𝓛 M) hz)
    (le_sup_right (a := Zl L) (b := NN 𝓛 M) hxn)

theorem MK_comm {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) {m : G} (hm : m ∈ MK 𝓛 L M) :
    ∀ y ∈ M, m * y = y * m := by
  obtain ⟨z, hz, n, hn, rfl⟩ := mem_sup_of_comm
    (fun n hn z hz => (Zl_comm_left hz (NN_le_L hcp M hn)).symm) hm
  intro y hy
  have h1 : n * y = y * n := ((Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM hn)) y hy).symm
  have h2 : z * y = y * z := Zl_comm_left hz (hcp.K_le_L hM hy)
  rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

theorem MK_of_center {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) {z : G} (hz : z ∈ M)
    (hzc : ∀ y ∈ M, z * y = y * z) : z ∈ MK 𝓛 L M := by
  have hLc : L ≤ Subgroup.centralizer ({z} : Set G) := by
    refine (le_of_eq hcp.gen).trans (sSup_le fun X hX => ?_)
    intro h hh
    rw [Subgroup.mem_centralizer_singleton_iff]
    by_cases hXM : X = M
    · subst hXM
      exact (hzc h hh).symm
    · have hhN : h ∈ NN 𝓛 M := (le_sSup ⟨hX, hXM⟩ : X ≤ NN 𝓛 M) hh
      exact ((Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM hhN)) z hz).symm
  have hzZ : z ∈ Zl L := by
    unfold Zl
    refine Subgroup.mem_inf.2 ⟨hcp.K_le_L hM hz, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc hh)
  unfold MK
  exact Subgroup.mem_sup_left hzZ

def supp (𝓛 : Set (Subgroup G)) (L : Subgroup G) (w : G) : Set (Subgroup G) :=
  {M | M ∈ 𝓛 ∧ w ∉ MK 𝓛 L M}

theorem supp_mul_subset (𝓛 : Set (Subgroup G)) (L : Subgroup G) (w v : G) :
    supp 𝓛 L (w * v) ⊆ supp 𝓛 L w ∪ supp 𝓛 L v := by
  rintro M ⟨hM, hwv⟩
  by_contra h
  simp only [Set.mem_union, not_or, supp, Set.mem_setOf_eq, not_and, not_not] at h
  exact hwv ((MK 𝓛 L M).mul_mem (h.1 hM) (h.2 hM))

theorem supp_inv (𝓛 : Set (Subgroup G)) (L : Subgroup G) (w : G) :
    supp 𝓛 L w⁻¹ = supp 𝓛 L w := by
  ext M
  simp only [supp, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hM, h⟩
    exact ⟨hM, fun h' => h ((MK 𝓛 L M).inv_mem h')⟩
  · rintro ⟨hM, h⟩
    exact ⟨hM, fun h' => h (by simpa using (MK 𝓛 L M).inv_mem h')⟩

theorem supp_eq_empty_central {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {w : G} (hwL : w ∈ L) (hw : supp 𝓛 L w = ∅) : w ∈ Zl L := by
  have hwM : ∀ M ∈ 𝓛, w ∈ MK 𝓛 L M := by
    intro M hM
    by_contra hcon
    have : M ∈ supp 𝓛 L w := ⟨hM, hcon⟩
    rw [hw] at this
    exact this
  have hLc : L ≤ Subgroup.centralizer ({w} : Set G) := by
    refine (le_of_eq hcp.gen).trans (sSup_le fun X hX => ?_)
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (MK_comm hcp hX (hwM X hX) y hy).symm
  unfold Zl
  refine Subgroup.mem_inf.2 ⟨hwL, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
  exact Subgroup.mem_centralizer_singleton_iff.1 (hLc hh)

theorem Zl_conj_le {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G)) :
    GLBConj x (Zl L) ≤ Zl L := by
  intro z hz
  rw [mem_gLBConj] at hz
  have hz' : x * z * x⁻¹ ∈ L ∧ x * z * x⁻¹ ∈ Subgroup.centralizer (L : Set G) := Subgroup.mem_inf.1 hz
  have hzL : z ∈ L := (Subgroup.mem_normalizer_iff.1 hx z).2 hz'.1
  refine Subgroup.mem_inf.2 ⟨hzL, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
  have hxh : x * h * x⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hx h).1 hh
  have e := (Subgroup.mem_centralizer_iff.1 hz'.2) (x * h * x⁻¹) hxh
  have e2 : x * (h * z) * x⁻¹ = x * (z * h) * x⁻¹ := by
    calc x * (h * z) * x⁻¹ = (x * h * x⁻¹) * (x * z * x⁻¹) := by group
      _ = (x * z * x⁻¹) * (x * h * x⁻¹) := e
      _ = x * (z * h) * x⁻¹ := by group
  calc h * z = x⁻¹ * (x * (h * z) * x⁻¹) * x := by group
    _ = x⁻¹ * (x * (z * h) * x⁻¹) * x := by rw [e2]
    _ = z * h := by group

theorem MK_conj_le {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {g : G} (hg : g ∈ B) {K : Subgroup G} (hK : K ∈ 𝓛) :
    GLBConj g (MK 𝓛 L K) ≤ MK 𝓛 L (GLBConj g K) := by
  unfold MK
  unfold GLBConj at *
  rw [Subgroup.map_sup]
  exact sup_le_sup (Zl_conj_le (hcp.norm hg)) (NN_conj_le hcp hg hK)

theorem W_cover_K₀ {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G)) {k : G} (hk : k ∈ K₀) :
    ∃ w ∈ Wof p B L K₀, k⁻¹ * w ∈ MK 𝓛 L K₀ := by
  refine ⟨dlProd b₀ k p, ?_, ?_⟩
  · have := dl_le_W hp hcp hK₀ hb₀ hb₀N hpK (MonoidHom.mem_range.2 ⟨⟨k, hk⟩, rfl⟩)
    rwa [dlHom_apply] at this
  · obtain ⟨hdk, hP⟩ := dlProd_eq_k_mul hp hcp hK₀ hb₀ hb₀N hk
    rw [hdk, ← mul_assoc, inv_mul_cancel, one_mul]
    have hPN : ((List.range (p - 1)).map fun j => cj b₀ k (j + 1)).prod ∈ NN 𝓛 K₀ :=
      Asub_le_NN hp hcp hK₀ hb₀ hb₀N hP
    exact (le_sup_right : NN 𝓛 K₀ ≤ Zl L ⊔ NN 𝓛 K₀) hPN

theorem W_cover {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {M : Subgroup G} (hM : M ∈ 𝓛) {m : G} (hm : m ∈ M) :
    ∃ w ∈ Wof p B L K₀, m⁻¹ * w ∈ MK 𝓛 L M := by
  obtain ⟨g, hg, hgM⟩ := hcp.trans K₀ hK₀ M hM
  have hmK : g * m * g⁻¹ ∈ K₀ := by
    rw [← mem_gLBConj, hgM]
    exact hm
  obtain ⟨w₀, hw₀, hk⟩ := W_cover_K₀ hp hcp hK₀ hpK hb₀ hb₀N hmK
  refine ⟨g⁻¹ * w₀ * g, ?_, ?_⟩
  · have hmem : g⁻¹ * w₀ * g ∈ GLBConj g (Wof p B L K₀) := by
      rw [mem_gLBConj]
      simpa [mul_assoc] using hw₀
    exact Wof_conj_le hcp hg hmem
  · have hmem : g⁻¹ * (g * m * g⁻¹)⁻¹ * w₀ * g ∈ GLBConj g (MK 𝓛 L K₀) := by
      rw [mem_gLBConj]
      have e : g * (g⁻¹ * (g * m * g⁻¹)⁻¹ * w₀ * g) * g⁻¹ = (g * m * g⁻¹)⁻¹ * w₀ := by group
      rw [e]
      exact hk
    have hsub := MK_conj_le hcp hg hK₀ hmem
    rw [hgM] at hsub
    have e2 : m⁻¹ * (g⁻¹ * w₀ * g) = g⁻¹ * (g * m * g⁻¹)⁻¹ * w₀ * g := by group
    rw [e2]
    exact hsub

theorem layer_le_self {p : ℕ} (X : Subgroup G) : GLAPLayer p X ≤ X := by
  unfold GLAPLayer
  exact sSup_le fun K hK => hK.1

theorem Wof_le_L {p : ℕ} {B L : Subgroup G} (K₀ : Subgroup G) : Wof p B L K₀ ≤ L :=
  sSup_le fun Z hZ => by
    obtain ⟨y, -, -, -, rfl⟩ := hZ
    exact (layer_le_self _).trans inf_le_left

def VT (W : Subgroup G) (𝓛 : Set (Subgroup G)) (L : Subgroup G) (T : Set (Subgroup G)) :
    Subgroup G where
  carrier := {v | v ∈ W ∧ supp 𝓛 L v ⊆ T}
  one_mem' := ⟨W.one_mem, fun M hM => absurd (MK 𝓛 L M).one_mem hM.2⟩
  mul_mem' := fun {a b} ha hb => ⟨W.mul_mem ha.1 hb.1, (supp_mul_subset 𝓛 L a b).trans
    (Set.union_subset ha.2 hb.2)⟩
  inv_mem' := fun {a} ha => ⟨W.inv_mem ha.1, by rw [supp_inv]; exact ha.2⟩

theorem supp_conj {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {w : G} (hw : w ∈ L) (v : G) :
    supp 𝓛 L (w * v * w⁻¹) = supp 𝓛 L v := by
  ext M
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨hM, fun hv => h ?_⟩
    exact MK_normal_L hcp hM hw hv
  · rintro ⟨hM, h⟩
    refine ⟨hM, fun hwv => h ?_⟩
    have := MK_normal_L hcp hM (L.inv_mem hw) hwv
    simpa [mul_assoc] using this

theorem star_lemma {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {M : Subgroup G} (hM : M ∈ 𝓛) {w₀ : G} (hw₀ : w₀ ∈ Wof p B L K₀)
    (hw₀M : M ∈ supp 𝓛 L w₀) :
    ∀ m ∈ M, ∃ v ∈ VT (Wof p B L K₀) 𝓛 L (supp 𝓛 L w₀), m⁻¹ * v ∈ MK 𝓛 L M := by
  have hWL : Wof p B L K₀ ≤ L := Wof_le_L K₀
  have hML : M ≤ L := hcp.K_le_L hM
  let A : Subgroup G :=
    { carrier := {k | k ∈ M ∧ ∃ v ∈ VT (Wof p B L K₀) 𝓛 L (supp 𝓛 L w₀), k⁻¹ * v ∈ MK 𝓛 L M}
      one_mem' := ⟨M.one_mem, 1, (VT (Wof p B L K₀) 𝓛 L (supp 𝓛 L w₀)).one_mem, by simp⟩
      mul_mem' := by
        rintro k k' ⟨hk, v, hv, hkv⟩ ⟨hk', v', hv', hk'v'⟩
        refine ⟨M.mul_mem hk hk', v * v', (VT _ _ _ _).mul_mem hv hv', ?_⟩
        have hconj := MK_normal_L hcp hM (L.inv_mem (hML hk')) hkv
        have e : (k * k')⁻¹ * (v * v') = (k'⁻¹ * (k⁻¹ * v) * k') * (k'⁻¹ * v') := by group
        rw [e]
        exact (MK 𝓛 L M).mul_mem (by simpa [mul_assoc] using hconj) hk'v'
      inv_mem' := by
        rintro k ⟨hk, v, hv, hkv⟩
        refine ⟨M.inv_mem hk, v⁻¹, (VT _ _ _ _).inv_mem hv, ?_⟩
        have h1 : k * (k⁻¹ * v)⁻¹ * k⁻¹ ∈ MK 𝓛 L M :=
          MK_normal_L hcp hM (hML hk) ((MK 𝓛 L M).inv_mem hkv)
        have e : (k⁻¹)⁻¹ * v⁻¹ = k * (k⁻¹ * v)⁻¹ * k⁻¹ := by group
        rw [e]
        exact h1 }
  have hAconj : ∀ a ∈ M, ∀ k ∈ A, a * k * a⁻¹ ∈ A := by
    intro a ha k hkA
    obtain ⟨hk, v, hv, hkv⟩ := hkA
    obtain ⟨w, hw, haw⟩ := W_cover hp hcp hK₀ hpK hb₀ hb₀N hM ha
    have hvW : v ∈ Wof p B L K₀ := hv.1
    have hv' : w * v * w⁻¹ ∈ VT (Wof p B L K₀) 𝓛 L (supp 𝓛 L w₀) := by
      refine ⟨(Wof p B L K₀).mul_mem ((Wof p B L K₀).mul_mem hw hvW)
        ((Wof p B L K₀).inv_mem hw), ?_⟩
      rw [supp_conj hcp (hWL hw) v]
      exact hv.2
    refine ⟨M.mul_mem (M.mul_mem ha hk) (M.inv_mem ha), w * v * w⁻¹, hv', ?_⟩
    have hwv : w = a * (a⁻¹ * w) := by group
    have e : (a * k * a⁻¹)⁻¹ * (w * v * w⁻¹) =
        a * ((k⁻¹ * v) * ((v⁻¹ * (a⁻¹ * w) * v) * (a⁻¹ * w)⁻¹)) * a⁻¹ := by
      rw [hwv]
      group
    rw [e]
    have hh1 : v⁻¹ * (a⁻¹ * w) * v ∈ MK 𝓛 L M := by
      have := MK_normal_L hcp hM (L.inv_mem (hWL hvW)) haw
      simpa [mul_assoc] using this
    exact MK_normal_L hcp hM (hML ha)
      ((MK 𝓛 L M).mul_mem hkv ((MK 𝓛 L M).mul_mem hh1 ((MK 𝓛 L M).inv_mem haw)))
  have hAnorm : (A.subgroupOf M).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hAconj g.1 g.2 n.1 hn
  have hk₀ : ∃ k₀ ∈ M, ∃ m₀ ∈ MK 𝓛 L M, w₀ = k₀ * m₀ := by
    have hL_le : L ≤ M ⊔ MK 𝓛 L M :=
      (L_le_sup_NN hcp hM).trans (sup_le_sup_left (le_sup_right : NN 𝓛 M ≤ MK 𝓛 L M) M)
    obtain ⟨k₀, hk₀, m₀, hm₀, h⟩ := mem_sup_of_comm
      (fun n hn x hx => MK_comm hcp hM hn x hx) (hL_le (hWL hw₀))
    exact ⟨k₀, hk₀, m₀, hm₀, h⟩
  obtain ⟨k₀, hk₀M, m₀, hm₀, hw₀dec⟩ := hk₀
  have hk₀A : k₀ ∈ A := by
    refine ⟨hk₀M, w₀, ⟨hw₀, subset_refl _⟩, ?_⟩
    rw [hw₀dec]
    have e : k₀⁻¹ * (k₀ * m₀) = m₀ := by group
    rw [e]
    exact hm₀
  have hk₀nc : (⟨k₀, hk₀M⟩ : ↥M) ∉ Subgroup.center ↥M := by
    intro hc
    apply hw₀M.2
    have hk₀MK : k₀ ∈ MK 𝓛 L M := by
      apply MK_of_center hcp hM hk₀M
      intro y hy
      have := Subgroup.mem_center_iff.1 hc ⟨y, hy⟩
      exact (congrArg Subtype.val this).symm
    rw [hw₀dec]
    exact (MK 𝓛 L M).mul_mem hk₀MK hm₀
  have hAtop : A.subgroupOf M = ⊤ := by
    by_contra hne
    have hcen := qs_normal_le_center (H := ↥M) (hcp.comp M hM).2.2 (A.subgroupOf M) hne
    exact hk₀nc (hcen (Subgroup.mem_subgroupOf.2 hk₀A))
  intro m hm
  have hmem : (⟨m, hm⟩ : ↥M) ∈ A.subgroupOf M := by
    rw [hAtop]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf.1 hmem).2

theorem qs_le_of_comm {K N : Subgroup G} (hq : CFSG.Open.IsQuasisimple K)
    (h : ∀ a ∈ K, ∀ b ∈ K, ⁅a, b⁆ ∈ N) : K ≤ N := by
  have hcomm_le : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ ≤ N.comap K.subtype := by
    refine Subgroup.commutator_le.2 (fun a _ b _ => ?_)
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact h _ a.2 _ b.2
  have htop : (⊤ : Subgroup K) ≤ N.comap K.subtype := by
    rw [← hq.1, commutator_def]
    exact hcomm_le
  intro x hx
  exact htop (Subgroup.mem_top (⟨x, hx⟩ : K))

theorem supp_commutator {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {x y : G} (hx : x ∈ L) (hy : y ∈ L) :
    supp 𝓛 L ⁅x, y⁆ ⊆ supp 𝓛 L x ∩ supp 𝓛 L y := by
  rintro M ⟨hM, hc⟩
  refine ⟨⟨hM, fun hxM => hc ?_⟩, ⟨hM, fun hyM => hc ?_⟩⟩
  · rw [commutatorElement_def]
    have h1 : y * x⁻¹ * y⁻¹ ∈ MK 𝓛 L M := MK_normal_L hcp hM hy ((MK 𝓛 L M).inv_mem hxM)
    rw [show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
    exact (MK 𝓛 L M).mul_mem hxM h1
  · rw [commutatorElement_def]
    have h1 : x * y * x⁻¹ ∈ MK 𝓛 L M := MK_normal_L hcp hM hx hyM
    rw [show x * y * x⁻¹ * y⁻¹ = (x * y * x⁻¹) * y⁻¹ by group]
    exact (MK 𝓛 L M).mul_mem h1 ((MK 𝓛 L M).inv_mem hyM)

theorem exists_noncomm_pair {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) :
    ∃ a ∈ M, ∃ b ∈ M, ⁅a, b⁆ ∉ MK 𝓛 L M := by
  by_contra h
  push_neg at h
  have hle := qs_le_of_comm (hcp.comp M hM).2.2 h
  exact qs_not_comm_subgroup (hcp.comp M hM).2.2
    (fun a ha b hb => MK_comm hcp hM (hle ha) b hb)

theorem singleton_decomp {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) {v : G} (hvL : v ∈ L)
    (hv : ∀ M' ∈ 𝓛, M' ≠ M → v ∈ MK 𝓛 L M') : ∃ k ∈ M, ∃ z ∈ Zl L, v = k * z := by
  have hsup : v ∈ M ⊔ NN 𝓛 M := (L_le_sup_NN hcp hM) hvL
  obtain ⟨k, hk, n, hn, rfl⟩ := mem_sup_of_comm
    (fun n hn x hx => (Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM hn)) x hx |>.symm)
    hsup
  have hnL : n ∈ L := NN_le_L hcp M hn
  have hcomm : ∀ M' ∈ 𝓛, ∀ y ∈ M', n * y = y * n := by
    intro M' hM' y hy
    by_cases hMM : M' = M
    · subst hMM
      exact (Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM' hn) y hy).symm
    · have hvM' : k * n ∈ MK 𝓛 L M' := hv M' hM' hMM
      have hkc : k * y = y * k := hcp.comm M hM M' hM' (Ne.symm hMM) k hk y hy
      have hvc : (k * n) * y = y * (k * n) := MK_comm hcp hM' hvM' y hy
      have : n * y = y * n := by
        calc n * y = k⁻¹ * (k * n) * y := by group
          _ = k⁻¹ * ((k * n) * y) := by group
          _ = k⁻¹ * (y * (k * n)) := by rw [hvc]
          _ = (k⁻¹ * y * k) * n := by group
          _ = (y * k⁻¹ * k) * n := by
              congr 1
              have hky : k⁻¹ * y = y * k⁻¹ := by
                calc k⁻¹ * y = k⁻¹ * (y * k) * k⁻¹ := by group
                  _ = k⁻¹ * (k * y) * k⁻¹ := by rw [hkc]
                  _ = y * k⁻¹ := by group
              rw [hky]
          _ = y * n := by group
      exact this
  have hnZ : n ∈ Zl L := by
    unfold Zl
    refine Subgroup.mem_inf.2 ⟨hnL, Subgroup.mem_centralizer_iff.2 (fun h hh => ?_)⟩
    have hLc : L ≤ Subgroup.centralizer ({n} : Set G) := by
      refine (le_of_eq hcp.gen).trans (sSup_le fun X hX => ?_)
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.2 (hcomm X hX y hy).symm
    exact Subgroup.mem_centralizer_singleton_iff.1 (hLc hh)
  exact ⟨k, hk, n, hnZ, rfl⟩

theorem comm_not_mem {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {M : Subgroup G} (hM : M ∈ 𝓛) {x z k₁ k₂ : G}
    (hx : x ∈ L) (hz : z ∈ L) (hk₁ : k₁ ∈ M) (hk₂ : k₂ ∈ M)
    (h₁ : k₁⁻¹ * x ∈ MK 𝓛 L M) (h₂ : k₂⁻¹ * z ∈ MK 𝓛 L M)
    (hc : ⁅k₁, k₂⁆ ∉ MK 𝓛 L M) : ⁅x, z⁆ ∉ MK 𝓛 L M := by
  intro hxz
  apply hc
  have hML : M ≤ L := hcp.K_le_L hM
  set N : Subgroup L := (MK 𝓛 L M).subgroupOf L with hNdef
  have hNn : N.Normal := by
    constructor
    intro n hn g
    rw [hNdef, Subgroup.mem_subgroupOf] at hn ⊢
    simpa using MK_normal_L hcp hM g.2 hn
  let π : L →* L ⧸ N := QuotientGroup.mk' N
  let a₁ : L := ⟨x, hx⟩
  let b₁ : L := ⟨z, hz⟩
  let c₁ : L := ⟨k₁, hML hk₁⟩
  let c₂ : L := ⟨k₂, hML hk₂⟩
  have hπa : π a₁ = π c₁ := by
    refine QuotientGroup.eq.2 ?_
    rw [hNdef, Subgroup.mem_subgroupOf]
    simpa [a₁, c₁] using (MK 𝓛 L M).inv_mem h₁
  have hπb : π b₁ = π c₂ := by
    refine QuotientGroup.eq.2 ?_
    rw [hNdef, Subgroup.mem_subgroupOf]
    simpa [b₁, c₂] using (MK 𝓛 L M).inv_mem h₂
  have hq : π ⁅a₁, b₁⁆ = π ⁅c₁, c₂⁆ := by
    rw [map_commutatorElement, map_commutatorElement, hπa, hπb]
  have hfin := QuotientGroup.eq.1 hq
  rw [hNdef, Subgroup.mem_subgroupOf] at hfin
  have hcoe1 : ((⁅a₁, b₁⁆ : L) : G) = ⁅x, z⁆ := by
    simp [commutatorElement_def, a₁, b₁]
  have hcoe2 : ((⁅c₁, c₂⁆ : L) : G) = ⁅k₁, k₂⁆ := by
    simp [commutatorElement_def, c₁, c₂]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hfin
  rw [hcoe1, hcoe2] at hfin
  have := (MK 𝓛 L M).mul_mem hxz hfin
  rwa [mul_inv_cancel_left] at this

def IsMinW (p : ℕ) (B L K₀ : Subgroup G) (𝓛 : Set (Subgroup G)) (w₀ : G) : Prop :=
  w₀ ∈ Wof p B L K₀ ∧ w₀ ∉ Zl L ∧ ∀ w ∈ Wof p B L K₀, w ∉ Zl L →
    (supp 𝓛 L w₀).ncard ≤ (supp 𝓛 L w).ncard

theorem Zl_le_MK (𝓛 : Set (Subgroup G)) (L M : Subgroup G) : Zl L ≤ MK 𝓛 L M := le_sup_left

theorem supp_finite (𝓛 : Set (Subgroup G)) (L : Subgroup G) (w : G) :
    (supp 𝓛 L w).Finite :=
  (Set.toFinite 𝓛).subset (fun M hM => hM.1)

theorem block_sub {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {w₀ y : G} (hmin : IsMinW p B L K₀ 𝓛 w₀) (hy : y ∈ Wof p B L K₀)
    {K : Subgroup G} (hK : K ∈ supp 𝓛 L w₀) (hKy : K ∈ supp 𝓛 L y) :
    supp 𝓛 L w₀ ⊆ supp 𝓛 L y := by
  classical
  by_contra hnot
  obtain ⟨M₀, hM₀T, hM₀y⟩ : ∃ M₀ ∈ supp 𝓛 L w₀, M₀ ∉ supp 𝓛 L y := by
    obtain ⟨M₀, h1, h2⟩ := Set.not_subset.1 hnot
    exact ⟨M₀, h1, h2⟩
  have hKM : K ∈ 𝓛 := hK.1
  obtain ⟨k₁, hk₁, k₂, hk₂, hc⟩ := exists_noncomm_pair hcp hKM
  obtain ⟨x, hxV, h₁⟩ := star_lemma hp hcp hK₀ hpK hb₀ hb₀N hKM hmin.1 hK k₁ hk₁
  obtain ⟨z, hzV, h₂⟩ := star_lemma hp hcp hK₀ hpK hb₀ hb₀N hKM hy hKy k₂ hk₂
  have hxL : x ∈ L := Wof_le_L K₀ hxV.1
  have hzL : z ∈ L := Wof_le_L K₀ hzV.1
  have hcW : ⁅x, z⁆ ∈ Wof p B L K₀ := by
    rw [commutatorElement_def]
    exact (Wof p B L K₀).mul_mem ((Wof p B L K₀).mul_mem ((Wof p B L K₀).mul_mem hxV.1 hzV.1)
      ((Wof p B L K₀).inv_mem hxV.1)) ((Wof p B L K₀).inv_mem hzV.1)
  have hcK : K ∈ supp 𝓛 L ⁅x, z⁆ :=
    ⟨hKM, comm_not_mem hcp hKM hxL hzL hk₁ hk₂ h₁ h₂ hc⟩
  have hcZl : ⁅x, z⁆ ∉ Zl L := fun h => hcK.2 (Zl_le_MK 𝓛 L K h)
  have hsupp_c : supp 𝓛 L ⁅x, z⁆ ⊆ supp 𝓛 L w₀ ∩ supp 𝓛 L y :=
    (supp_commutator hcp hxL hzL).trans (Set.inter_subset_inter hxV.2 hzV.2)
  have hmin' := hmin.2.2 ⁅x, z⁆ hcW hcZl
  have hlt : supp 𝓛 L ⁅x, z⁆ ⊂ supp 𝓛 L w₀ :=
    ⟨fun M hM => (hsupp_c hM).1, fun h => hM₀y ((hsupp_c (h hM₀T)).2)⟩
  have := Set.ncard_lt_ncard hlt (supp_finite 𝓛 L w₀)
  omega

theorem gLBConj_inv_gLBConj (g : G) (K : Subgroup G) : GLBConj g⁻¹ (GLBConj g K) = K := by
  simpa using gLBConj_gLBConj_inv g⁻¹ K

theorem MK_conj_eq {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {g : G} (hg : g ∈ B) {K : Subgroup G} (hK : K ∈ 𝓛) :
    GLBConj g (MK 𝓛 L K) = MK 𝓛 L (GLBConj g K) := by
  refine le_antisymm (MK_conj_le hcp hg hK) ?_
  intro x hx
  rw [mem_gLBConj]
  have hK' : GLBConj g K ∈ 𝓛 := hcp.conj_mem hg hK
  have hy : g * x * g⁻¹ ∈ GLBConj g⁻¹ (MK 𝓛 L (GLBConj g K)) := by
    rw [mem_gLBConj]
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  have h2 := MK_conj_le hcp (B.inv_mem hg) hK'
  rw [gLBConj_inv_gLBConj] at h2
  exact h2 hy

theorem supp_conj_formula {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {g : G} (hg : g ∈ B) (w : G) (M : Subgroup G) :
    M ∈ supp 𝓛 L (g * w * g⁻¹) ↔ GLBConj g M ∈ supp 𝓛 L w := by
  constructor
  · rintro ⟨hM, h⟩
    refine ⟨hcp.conj_mem hg hM, fun hw => h ?_⟩
    rw [← MK_conj_eq hcp hg hM] at hw
    exact mem_gLBConj.1 hw
  · rintro ⟨hK1, hK2⟩
    have hM : M ∈ 𝓛 := by
      have := hcp.conj_mem (B.inv_mem hg) hK1
      rwa [gLBConj_inv_gLBConj] at this
    refine ⟨hM, fun h => hK2 ?_⟩
    rw [← MK_conj_eq hcp hg hM]
    exact mem_gLBConj.2 h

theorem gLBConj_conj_inv (g : G) (K : Subgroup G) : GLBConj g (GLBConj g⁻¹ K) = K := by
  simpa using gLBConj_inv_gLBConj g⁻¹ K

theorem supp_conj_ncard {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {g : G} (hg : g ∈ B) (w : G) :
    (supp 𝓛 L (g * w * g⁻¹)).ncard = (supp 𝓛 L w).ncard := by
  have himg : supp 𝓛 L (g * w * g⁻¹) = (fun M => GLBConj g⁻¹ M) '' supp 𝓛 L w := by
    ext M
    constructor
    · intro hM
      exact ⟨GLBConj g M, (supp_conj_formula hcp hg w M).1 hM, gLBConj_inv_gLBConj g M⟩
    · rintro ⟨N, hN, rfl⟩
      rw [supp_conj_formula hcp hg, gLBConj_conj_inv]
      exact hN
  rw [himg]
  refine Set.ncard_image_of_injective _ ?_
  intro X Y h
  have h' : GLBConj g⁻¹ X = GLBConj g⁻¹ Y := h
  calc X = GLBConj g (GLBConj g⁻¹ X) := (gLBConj_conj_inv g X).symm
    _ = GLBConj g (GLBConj g⁻¹ Y) := by rw [h']
    _ = Y := gLBConj_conj_inv g Y

theorem comm_mul_right_central {x y c : G} (hc : c * y = y * c) : ⁅x * c, y⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hy : c * y * c⁻¹ = y := by rw [hc]; group
  calc x * c * y * (x * c)⁻¹ * y⁻¹ = x * (c * y * c⁻¹) * x⁻¹ * y⁻¹ := by group
    _ = x * y * x⁻¹ * y⁻¹ := by rw [hy]

theorem comm_mul_right_of_comm {x y c : G} (hc : c * x = x * c) : ⁅x, y * c⁆ = ⁅x, y⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have hx : x⁻¹ * c = c * x⁻¹ := by
    calc x⁻¹ * c = x⁻¹ * (c * x) * x⁻¹ := by group
      _ = x⁻¹ * (x * c) * x⁻¹ := by rw [hc]
      _ = c * x⁻¹ := by group
  calc x * (y * c) * x⁻¹ * (y * c)⁻¹ = x * y * (c * x⁻¹) * c⁻¹ * y⁻¹ := by group
    _ = x * y * (x⁻¹ * c) * c⁻¹ * y⁻¹ := by rw [hx]
    _ = x * y * x⁻¹ * y⁻¹ := by group

theorem comm_Zl_pair {L : Subgroup G} {k k' z w : G} (hk : k ∈ L) (hk' : k' ∈ L)
    (hz : z ∈ Zl L) (hw : w ∈ Zl L) : ⁅k * z, k' * w⁆ = ⁅k, k'⁆ := by
  have hzc : ∀ y ∈ L, z * y = y * z := fun y hy => Zl_comm_left hz hy
  have hwc : ∀ y ∈ L, w * y = y * w := fun y hy => Zl_comm_left hw hy
  have hzw : z * w = w * z := (hwc z hz.1).symm
  have h1 : z * (k' * w) = (k' * w) * z := by
    calc z * (k' * w) = (z * k') * w := by group
      _ = (k' * z) * w := by rw [hzc k' hk']
      _ = k' * (z * w) := by group
      _ = k' * (w * z) := by rw [hzw]
      _ = (k' * w) * z := by group
  rw [comm_mul_right_central h1, comm_mul_right_of_comm (hwc k hk)]

theorem exists_good_of_singleton {p : ℕ} (hp : p.Prime) {B L : Subgroup G}
    {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛)
    (hpK : p ∣ Nat.card K₀) {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {w₀ : G} (hmin : IsMinW p B L K₀ 𝓛 w₀) {M : Subgroup G}
    (hMT : M ∈ supp 𝓛 L w₀) (hsing : ∀ M' ∈ supp 𝓛 L w₀, M' = M) {a : G} (ha : a ∈ M) :
    ∃ k ∈ M, ∃ z ∈ Zl L, k * z ∈ Wof p B L K₀ ∧ a⁻¹ * k ∈ MK 𝓛 L M := by
  obtain ⟨v, hv, hav⟩ := star_lemma hp hcp hK₀ hpK hb₀ hb₀N hMT.1 hmin.1 hMT a ha
  have hvW : v ∈ Wof p B L K₀ := hv.1
  have hvL : v ∈ L := Wof_le_L K₀ hvW
  have hvM : ∀ M' ∈ 𝓛, M' ≠ M → v ∈ MK 𝓛 L M' := by
    intro M' hM' hne
    by_contra hc
    have hmem : M' ∈ supp 𝓛 L v := ⟨hM', hc⟩
    exact hne (hsing M' (hv.2 hmem))
  obtain ⟨k, hk, z, hz, rfl⟩ := singleton_decomp hcp hMT.1 hvL hvM
  refine ⟨k, hk, z, hz, hvW, ?_⟩
  have e : a⁻¹ * k = (a⁻¹ * (k * z)) * z⁻¹ := by group
  rw [e]
  exact (MK 𝓛 L M).mul_mem hav (Zl_le_MK 𝓛 L M ((Zl L).inv_mem hz))

theorem singleton_case {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {w₀ : G} (hmin : IsMinW p B L K₀ 𝓛 w₀) {M : Subgroup G} (hMT : M ∈ supp 𝓛 L w₀)
    (hsing : ∀ M' ∈ supp 𝓛 L w₀, M' = M) : K₀ ≤ Wof p B L K₀ := by
  have hM : M ∈ 𝓛 := hMT.1
  have hML : M ≤ L := hcp.K_le_L hM
  have hMW : M ≤ Wof p B L K₀ := by
    refine qs_le_of_comm (hcp.comp M hM).2.2 ?_
    intro a ha b hb
    obtain ⟨ka, hka, za, hza, hkaW, hau⟩ :=
      exists_good_of_singleton hp hcp hK₀ hpK hb₀ hb₀N hmin hMT hsing ha
    obtain ⟨kb, hkb, zb, hzb, hkbW, hbu⟩ :=
      exists_good_of_singleton hp hcp hK₀ hpK hb₀ hb₀N hmin hMT hsing hb
    have hcomm_b : Commute (a⁻¹ * ka) b := MK_comm hcp hM hau b hb
    have hcomm_a : Commute (b⁻¹ * kb) ka := MK_comm hcp hM hbu ka hka
    have e1 : ⁅a, b⁆ = ⁅ka, b⁆ := by
      have := comm_mul_right_central (x := ka) (y := b) (c := (a⁻¹ * ka)⁻¹) hcomm_b.inv_left.eq
      rw [← this]
      congr 1
      group
    have e2 : ⁅ka, b⁆ = ⁅ka, kb⁆ := by
      have hd : Commute ((b⁻¹ * kb)⁻¹) ka := hcomm_a.inv_left
      have := comm_mul_right_of_comm (x := ka) (y := kb) (c := (b⁻¹ * kb)⁻¹) hd.eq
      rw [← this]
      congr 1
      group
    rw [e1, e2, ← comm_Zl_pair (hML hka) (hML hkb) hza hzb, commutatorElement_def]
    exact (Wof p B L K₀).mul_mem ((Wof p B L K₀).mul_mem ((Wof p B L K₀).mul_mem hkaW hkbW)
      ((Wof p B L K₀).inv_mem hkaW)) ((Wof p B L K₀).inv_mem hkbW)
  obtain ⟨x, hx, hxM⟩ := hcp.trans K₀ hK₀ M hM
  have hK : GLBConj x⁻¹ M ≤ Wof p B L K₀ :=
    (gLBConj_mono x⁻¹ hMW).trans (Wof_conj_le hcp (B.inv_mem hx))
  rw [← hxM, gLBConj_inv_gLBConj] at hK
  exact hK

theorem inB_comm {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {x y : G} (hx : x ∈ B) (hy : y ∈ B) : x * y = y * x :=
  congrArg Subtype.val (hcp.elem.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)

theorem mem_norm_of_gLBConj_eq {g : G} {Q : Subgroup G} (h : GLBConj g Q = Q) :
    g ∈ Subgroup.normalizer (Q : Set G) := by
  have h1 : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) := by
    have h2 := gLBConj_eq_norm Q (show GLBConj g Q = GLBConj 1 Q by rw [h, gLBConj_one])
    rwa [one_mul] at h2
  have h3 := (Subgroup.normalizer (Q : Set G)).inv_mem h1
  rwa [inv_inv] at h3

theorem gLBConj_mul_of_norm {H : Subgroup G} {g n : G}
    (hn : n ∈ Subgroup.normalizer (GLBConj g H : Set G)) : GLBConj (g * n) H = GLBConj g H := by
  rw [← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer hn]

theorem norm_of_comp {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {n : G} (hn : n ∈ B)
    (hnK : n ∈ Subgroup.normalizer (K₀ : Set G)) {M : Subgroup G} (hM : M ∈ 𝓛) :
    n ∈ Subgroup.normalizer (M : Set G) := by
  obtain ⟨c, hc, hcM⟩ := hcp.trans K₀ hK₀ M hM
  rw [← hcM]
  apply mem_norm_of_gLBConj_eq
  rw [gLBConj_gLBConj, inB_comm hcp hc hn, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer hnK]

theorem fix_of_norm_comp {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {n : G} (hn : n ∈ B)
    (hnK : n ∈ Subgroup.normalizer (K₀ : Set G)) {M : Subgroup G} (hM : M ∈ 𝓛) :
    GLBConj n M = M :=
  gLBConj_eq_of_mem_normalizer (norm_of_comp hcp hK₀ hn hnK hM)

theorem cent_of_conj_comp {x c : G} (hc : c * x = x * c) {K K' : Subgroup G}
    (h : GLBConj c K = K') (hK : ∀ y ∈ K, x * y = y * x) : ∀ y ∈ K', x * y = y * x := by
  intro y hy'
  rw [← h, mem_gLBConj] at hy'
  have h1 := hK _ hy'
  have hinv : c⁻¹ * x * c = x := by rw [mul_assoc, ← hc]; group
  have e1 : c⁻¹ * (x * (c * y * c⁻¹)) * c = x * y := by
    calc c⁻¹ * (x * (c * y * c⁻¹)) * c = (c⁻¹ * x * c) * y := by group
      _ = x * y := by rw [hinv]
  have e2 : c⁻¹ * (c * y * c⁻¹ * x) * c = y * x := by
    calc c⁻¹ * (c * y * c⁻¹ * x) * c = y * (c⁻¹ * x * c) := by group
      _ = y * x := by rw [hinv]
  have h2 : c⁻¹ * (x * (c * y * c⁻¹)) * c = c⁻¹ * (c * y * c⁻¹ * x) * c := by rw [h1]
  rw [e1, e2] at h2
  exact h2

theorem zpow_gen_int {p : ℕ} {b : G} (hbp : b ^ p = 1) {e u v : ℤ}
    (huv : u * (p : ℤ) + v * e = 1) : (b ^ e) ^ v = b := by
  have key : e * v = 1 - (p : ℤ) * u := by linear_combination huv
  rw [← zpow_mul, key, zpow_sub, zpow_one, zpow_mul, zpow_natCast, hbp, one_zpow, inv_one, mul_one]

theorem central_of_MK {p : ℕ} {B L : Subgroup G} {𝓛 : Set (Subgroup G)} (hcp : CPData p B L 𝓛)
    {M : Subgroup G} (hM : M ∈ 𝓛) {y : G} (hy : y ∈ MK 𝓛 L M) : ∀ t ∈ M, y * t = t * y := by
  obtain ⟨z, hz, n, hn, rfl⟩ := mem_sup_of_comm
    (fun n hn z hz => (Zl_comm_left hz (NN_le_L hcp M hn)).symm) hy
  intro t ht
  have h1 : n * t = t * n :=
    ((Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hM hn)) t ht).symm
  have h2 : z * t = t * z := Zl_comm_left hz (hcp.K_le_L hM ht)
  rw [mul_assoc, h1, ← mul_assoc, h2, mul_assoc]

theorem dlProd_mem_W {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b : G} (hb : b ∈ B) (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {k : G} (hk : k ∈ K₀) :
    dlProd b k p ∈ Wof p B L K₀ := by
  have h := dl_le_W hp hcp hK₀ hb hbN hpK (MonoidHom.mem_range.2 ⟨⟨k, hk⟩, rfl⟩)
  rwa [dlHom_apply] at h

theorem dl_split_NN {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) {b : G} (hb : b ∈ B)
    (hbN : b ∉ Subgroup.normalizer (K₀ : Set G)) {k : G} (hk : k ∈ K₀) :
    ∃ P ∈ NN 𝓛 K₀, dlProd b k p = k * P := by
  obtain ⟨h, hP⟩ := dlProd_eq_k_mul hp hcp hK₀ hb hbN hk
  exact ⟨_, Asub_le_NN hp hcp hK₀ hb hbN hP, h⟩

theorem W_not_le_Zl {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G)) :
    ∃ w, w ∈ Wof p B L K₀ ∧ w ∉ Zl L := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hq : CFSG.Open.IsQuasisimple K₀ := (hcp.comp K₀ hK₀).2.2
  obtain ⟨kk, hkk, -⟩ := exists_noncentral_pElt hp hq hpK
  have hk : (kk : G) ∈ K₀ := kk.2
  refine ⟨dlProd b₀ (kk : G) p, dlProd_mem_W hp hcp hK₀ hpK hb₀ hb₀N hk, fun hwZ => ?_⟩
  obtain ⟨P, hP, hPe⟩ := dl_split_NN hp hcp hK₀ hb₀ hb₀N hk
  rw [hPe] at hwZ
  apply hkk
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have hyL : (g : G) ∈ L := hcp.K_le_L hK₀ g.2
  have hPc : (g : G) * P = P * (g : G) :=
    Subgroup.mem_centralizer_iff.1 (NN_le_centralizer hcp hK₀ hP) (g : G) g.2
  have hPinv : (g : G) * P⁻¹ = P⁻¹ * (g : G) :=
    (Commute.inv_right (show Commute (g : G) P from hPc)).eq
  have hwy : ((kk : G) * P) * (g : G) = (g : G) * ((kk : G) * P) := Zl_comm_left hwZ hyL
  have hkw : (kk : G) = ((kk : G) * P) * P⁻¹ := by group
  calc (g : G) * (kk : G) = (g : G) * (((kk : G) * P) * P⁻¹) := by rw [← hkw]
    _ = ((g : G) * ((kk : G) * P)) * P⁻¹ := by group
    _ = (((kk : G) * P) * (g : G)) * P⁻¹ := by rw [hwy.symm]
    _ = ((kk : G) * P) * ((g : G) * P⁻¹) := by group
    _ = ((kk : G) * P) * (P⁻¹ * (g : G)) := by rw [hPinv]
    _ = (kk : G) * (g : G) := by group

theorem exists_minW {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G)) :
    ∃ w₀ : G, IsMinW p B L K₀ 𝓛 w₀ := by
  obtain ⟨w, hw⟩ := W_not_le_Zl hp hcp hK₀ hpK hb₀ hb₀N
  obtain ⟨w₀, hw₀, hmin⟩ := Set.exists_min_image {v : G | v ∈ Wof p B L K₀ ∧ v ∉ Zl L}
    (fun v => (supp 𝓛 L v).ncard) (Set.toFinite _) ⟨w, hw⟩
  refine ⟨w₀, ?_⟩
  unfold IsMinW
  exact ⟨hw₀.1, hw₀.2, fun v hv hvZ => hmin v ⟨hv, hvZ⟩⟩

theorem r1_two_case {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    (hR1 : ∀ b' ∈ B, ∃ e : ℤ, b' * (b₀ ^ e)⁻¹ ∈ Subgroup.normalizer (K₀ : Set G))
    {w₀ : G} (hmin : IsMinW p B L K₀ 𝓛 w₀) {M₁ M₂ : Subgroup G}
    (h1 : M₁ ∈ supp 𝓛 L w₀) (h2 : M₂ ∈ supp 𝓛 L w₀) (hne : M₁ ≠ M₂) :
    ∀ M ∈ 𝓛, M ∈ supp 𝓛 L w₀ := by
  have hbp : b₀ ^ p = 1 := hcp.elem.2 b₀ hb₀
  have hcommB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => inB_comm hcp hx hy
  obtain ⟨s, hs, hsM⟩ := hcp.trans M₂ h2.1 M₁ h1.1
  have hsN : s ∉ Subgroup.normalizer (K₀ : Set G) := by
    intro hsK
    apply hne
    rw [← hsM]
    exact fix_of_norm_comp hcp hK₀ hs hsK h2.1
  obtain ⟨e₀, he₀⟩ := hR1 s hs
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : G, n₀ = s * (b₀ ^ e₀)⁻¹ := ⟨_, rfl⟩
  have hn₀N : n₀ ∈ Subgroup.normalizer (K₀ : Set G) := by rw [hn₀]; exact he₀
  have hn₀B : n₀ ∈ B := by rw [hn₀]; exact B.mul_mem hs (B.inv_mem (B.zpow_mem hb₀ e₀))
  have hn₀iB : n₀⁻¹ ∈ B := B.inv_mem hn₀B
  have hbe : b₀ ^ e₀ = n₀⁻¹ * s := by rw [hn₀]; group
  have hpe : ¬ ((p : ℤ) ∣ e₀) := by
    rintro ⟨m, hm⟩
    apply hsN
    have hb : b₀ ^ e₀ = 1 := by rw [hm, zpow_mul, zpow_natCast, hbp, one_zpow]
    have hs' : s = n₀ := by rw [hn₀, hb, inv_one, mul_one]
    rw [hs']
    exact hn₀N
  obtain ⟨u, v, huv⟩ := (_root_.Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp)).2 hpe
  have hb0 : b₀ = (n₀⁻¹ * s) ^ v := by
    rw [← hbe]
    exact (zpow_gen_int hbp huv).symm
  have hcs : Commute n₀⁻¹ s := hcommB _ hn₀iB _ hs
  have hb0' : b₀ = n₀⁻¹ ^ v * s ^ v := by
    rw [hb0]
    exact hcs.mul_zpow v
  have hcv : Commute (n₀⁻¹ ^ v) (s ^ v) := hcommB _ (B.zpow_mem hn₀iB v) _ (B.zpow_mem hs v)
  have hgen : ∀ b ∈ B, ∃ t : ℤ, ∃ n ∈ B, n ∈ Subgroup.normalizer (K₀ : Set G) ∧
      b = s ^ t * n := by
    intro b hb
    obtain ⟨eb, heb⟩ := hR1 b hb
    obtain ⟨nb, hnb⟩ : ∃ nb : G, nb = b * (b₀ ^ eb)⁻¹ := ⟨_, rfl⟩
    have hnbN : nb ∈ Subgroup.normalizer (K₀ : Set G) := by rw [hnb]; exact heb
    have hnbB : nb ∈ B := by rw [hnb]; exact B.mul_mem hb (B.inv_mem (B.zpow_mem hb₀ eb))
    have hX : (n₀⁻¹ ^ v) ^ eb ∈ B := B.zpow_mem (B.zpow_mem hn₀iB v) eb
    have hXN : (n₀⁻¹ ^ v) ^ eb ∈ Subgroup.normalizer (K₀ : Set G) :=
      (Subgroup.normalizer (K₀ : Set G)).zpow_mem
        ((Subgroup.normalizer (K₀ : Set G)).zpow_mem
          ((Subgroup.normalizer (K₀ : Set G)).inv_mem hn₀N) v) eb
    have hY : (s ^ v) ^ eb ∈ B := B.zpow_mem (B.zpow_mem hs v) eb
    have hbeb : b₀ ^ eb = (n₀⁻¹ ^ v) ^ eb * (s ^ v) ^ eb := by
      rw [hb0', hcv.mul_zpow]
    refine ⟨v * eb, nb * (n₀⁻¹ ^ v) ^ eb, B.mul_mem hnbB hX,
      (Subgroup.normalizer (K₀ : Set G)).mul_mem hnbN hXN, ?_⟩
    have hb_eq : b = nb * b₀ ^ eb := by rw [hnb]; group
    have hc2 := hcommB (nb * (n₀⁻¹ ^ v) ^ eb) (B.mul_mem hnbB hX) _ hY
    rw [hb_eq, hbeb, zpow_mul, ← hc2, mul_assoc]
  have hy : s * w₀ * s⁻¹ ∈ Wof p B L K₀ := by
    have h1' : s⁻¹ * (s * w₀ * s⁻¹) * s⁻¹⁻¹ ∈ Wof p B L K₀ := by
      rw [show s⁻¹ * (s * w₀ * s⁻¹) * s⁻¹⁻¹ = w₀ by group]
      exact hmin.1
    exact Wof_conj_le hcp (B.inv_mem hs) (mem_gLBConj.2 h1')
  have hm2 : M₂ ∈ supp 𝓛 L (s * w₀ * s⁻¹) :=
    (supp_conj_formula hcp hs w₀ M₂).2 (by rw [hsM]; exact h1)
  have hsub := block_sub hp hcp hK₀ hpK hb₀ hb₀N hmin hy h2 hm2
  have hSeq : supp 𝓛 L w₀ = supp 𝓛 L (s * w₀ * s⁻¹) :=
    Set.eq_of_subset_of_ncard_le hsub (supp_conj_ncard hcp hs w₀).le (supp_finite _ _ _)
  have hstab : ∀ M : Subgroup G, M ∈ supp 𝓛 L w₀ ↔ GLBConj s M ∈ supp 𝓛 L w₀ := by
    intro M
    have hiff := supp_conj_formula hcp hs w₀ M
    rw [← hSeq] at hiff
    exact hiff
  have hpow : ∀ t : ℤ, ∀ M ∈ supp 𝓛 L w₀, GLBConj (s ^ t) M ∈ supp 𝓛 L w₀ := by
    intro t
    refine zpow_induction_right (g := s)
      (P := fun a => ∀ M ∈ supp 𝓛 L w₀, GLBConj a M ∈ supp 𝓛 L w₀) ?_ ?_ ?_ t
    · intro M hM
      rw [gLBConj_one]
      exact hM
    · intro a ha M hM
      rw [← gLBConj_gLBConj]
      exact (hstab _).1 (ha M hM)
    · intro a ha M hM
      rw [← gLBConj_gLBConj]
      exact (hstab _).2 (by rw [gLBConj_conj_inv]; exact ha M hM)
  intro M' hM'
  obtain ⟨b, hb, hbM⟩ := hcp.trans M₂ h2.1 M' hM'
  obtain ⟨t, n, hnB, hnN, hbn⟩ := hgen b hb
  rw [← hbM, hbn, ← gLBConj_gLBConj,
    fix_of_norm_comp hcp hK₀ hnB hnN (hcp.conj_mem (B.zpow_mem hs t) h2.1)]
  exact hpow t M₂ h2

theorem r1_full_case {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    {w₀ : G} (hmin : IsMinW p B L K₀ 𝓛 w₀) (hS : ∀ M ∈ 𝓛, M ∈ supp 𝓛 L w₀)
    {x : G} (hxB : x ∈ B) (hxN : x ∈ Subgroup.normalizer (K₀ : Set G)) (hx1 : x ≠ 1)
    (hC : ∀ c ∈ B, c ≠ 1 → c ∉ Subgroup.centralizer (L : Set G)) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hbp : b₀ ^ p = 1 := hcp.elem.2 b₀ hb₀
  have hcx : Commute b₀ x := inB_comm hcp hb₀ hxB
  have hSeq : supp 𝓛 L w₀ = 𝓛 := Set.Subset.antisymm (fun M hM => hM.1) hS
  obtain ⟨m, hm⟩ : ∃ m : ℕ, p = m + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hK₁𝓛 : GLBConj b₀ K₀ ∈ 𝓛 := hcp.conj_mem hb₀ hK₀
  have hxK₁ : x ∈ Subgroup.normalizer (GLBConj b₀ K₀ : Set G) :=
    norm_of_comp hcp hK₀ hxB hxN hK₁𝓛
  have hbxB : b₀ * x ∈ B := B.mul_mem hb₀ hxB
  have hbxN : b₀ * x ∉ Subgroup.normalizer (K₀ : Set G) := by
    intro h
    apply hb₀N
    have e : b₀ = b₀ * x * x⁻¹ := by group
    rw [e]
    exact (Subgroup.normalizer (K₀ : Set G)).mul_mem h
      ((Subgroup.normalizer (K₀ : Set G)).inv_mem hxN)
  have hxpow : ∀ i : ℕ, GLBConj ((b₀ * x) ^ i) K₀ = GLBConj (b₀ ^ i) K₀ := by
    intro i
    have hn : x ^ i ∈ Subgroup.normalizer (GLBConj (b₀ ^ i) K₀ : Set G) :=
      Subgroup.pow_mem _ (norm_of_comp hcp hK₀ hxB hxN (hcp.conj_mem (B.pow_mem hb₀ i) hK₀)) i
    rw [hcx.mul_pow]
    exact gLBConj_mul_of_norm hn
  have hbxK : GLBConj (b₀ * x) K₀ = GLBConj b₀ K₀ := by
    have h := hxpow 1
    rwa [pow_one, pow_one] at h
  have hne1 : ∀ i : ℕ, 2 ≤ i → i < p → GLBConj (b₀ ^ i) K₀ ≠ GLBConj b₀ K₀ := by
    intro i hi2 hip heq
    apply orb_ne hp hcp hbp hb₀N hip hp.one_lt (show i ≠ 1 by omega)
    rw [pow_one]
    exact heq
  have hne2 : ∀ i : ℕ, 2 ≤ i → i < p → GLBConj ((b₀ * x) ^ i) K₀ ≠ GLBConj b₀ K₀ := by
    intro i hi2 hip
    rw [hxpow i]
    exact hne1 i hi2 hip
  have hdec : ∀ b k : G, dlProd b k p = k * (cj b k 1 * Rprod m b k) := by
    intro b k
    rw [hm]
    exact dlProd_split b k m
  have hRmem : ∀ b : G, (∀ j : ℕ, j < m → GLBConj (b ^ (j + 2)) K₀ ∈ 𝓛 ∧
      GLBConj (b ^ (j + 2)) K₀ ≠ GLBConj b₀ K₀) →
      ∀ k ∈ K₀, Rprod m b k ∈ MK 𝓛 L (GLBConj b₀ K₀) := by
    intro b hb k hk
    unfold Rprod
    have hprod : ((List.range m).map fun j => cj b k (j + 2)).prod ∈
        NN 𝓛 (GLBConj b₀ K₀) := by
      apply Subgroup.list_prod_mem
      intro z hz
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hz
      obtain ⟨hM, hne⟩ := hb j (List.mem_range.1 hj)
      exact (le_sSup ⟨hM, hne⟩ : GLBConj (b ^ (j + 2)) K₀ ≤ NN 𝓛 (GLBConj b₀ K₀))
        (cj_mem_Kj hk (j + 2))
    exact (le_sup_right : NN 𝓛 (GLBConj b₀ K₀) ≤ MK 𝓛 L (GLBConj b₀ K₀)) hprod
  have hb₀R : ∀ j : ℕ, j < m → GLBConj (b₀ ^ (j + 2)) K₀ ∈ 𝓛 ∧
      GLBConj (b₀ ^ (j + 2)) K₀ ≠ GLBConj b₀ K₀ :=
    fun j hj => ⟨hcp.conj_mem (B.pow_mem hb₀ _) hK₀, hne1 (j + 2) (by omega) (by omega)⟩
  have hbxR : ∀ j : ℕ, j < m → GLBConj ((b₀ * x) ^ (j + 2)) K₀ ∈ 𝓛 ∧
      GLBConj ((b₀ * x) ^ (j + 2)) K₀ ≠ GLBConj b₀ K₀ :=
    fun j hj => ⟨by rw [hxpow]; exact hcp.conj_mem (B.pow_mem hb₀ _) hK₀,
      hne2 (j + 2) (by omega) (by omega)⟩
  have hRq0 : ∀ k ∈ K₀, Rprod m b₀ k ∈ MK 𝓛 L (GLBConj b₀ K₀) := hRmem b₀ hb₀R
  have hRq1 : ∀ k ∈ K₀, Rprod m (b₀ * x) k ∈ MK 𝓛 L (GLBConj b₀ K₀) := hRmem (b₀ * x) hbxR
  have hzW : ∀ k ∈ K₀, (dlProd b₀ k p)⁻¹ * dlProd (b₀ * x) k p ∈ Wof p B L K₀ := fun k hk =>
    (Wof p B L K₀).mul_mem ((Wof p B L K₀).inv_mem (dlProd_mem_W hp hcp hK₀ hpK hb₀ hb₀N hk))
      (dlProd_mem_W hp hcp hK₀ hpK hbxB hbxN hk)
  have hzMK : ∀ k ∈ K₀, (dlProd b₀ k p)⁻¹ * dlProd (b₀ * x) k p ∈ MK 𝓛 L K₀ := by
    intro k hk
    obtain ⟨P₀, hP₀, e₀⟩ := dl_split_NN hp hcp hK₀ hb₀ hb₀N hk
    obtain ⟨P₁, hP₁, e₁⟩ := dl_split_NN hp hcp hK₀ hbxB hbxN hk
    rw [e₀, e₁]
    have e : (k * P₀)⁻¹ * (k * P₁) = P₀⁻¹ * P₁ := by group
    rw [e]
    exact (le_sup_right : NN 𝓛 K₀ ≤ MK 𝓛 L K₀)
      ((NN 𝓛 K₀).mul_mem ((NN 𝓛 K₀).inv_mem hP₀) hP₁)
  have hzZl : ∀ k ∈ K₀, (dlProd b₀ k p)⁻¹ * dlProd (b₀ * x) k p ∈ Zl L := by
    intro k hk
    by_contra hzZ
    have h1 := hmin.2.2 _ (hzW k hk) hzZ
    have h2 : supp 𝓛 L ((dlProd b₀ k p)⁻¹ * dlProd (b₀ * x) k p) ⊂ 𝓛 :=
      (Set.ssubset_iff_of_subset (fun M hM => hM.1)).2
        ⟨K₀, hK₀, fun hK => hK.2 (hzMK k hk)⟩
    have h3 := Set.ncard_lt_ncard h2 (Set.toFinite 𝓛)
    have h4 : (supp 𝓛 L w₀).ncard = 𝓛.ncard := by rw [hSeq]
    omega
  have hQ : ∀ k ∈ K₀, (cj b₀ k 1)⁻¹ * cj (b₀ * x) k 1 ∈ MK 𝓛 L (GLBConj b₀ K₀) := by
    intro k hk
    have e : (cj b₀ k 1)⁻¹ * cj (b₀ * x) k 1 =
        Rprod m b₀ k * ((dlProd b₀ k p)⁻¹ * dlProd (b₀ * x) k p) * (Rprod m (b₀ * x) k)⁻¹ := by
      rw [hdec b₀ k, hdec (b₀ * x) k]
      group
    rw [e]
    exact (MK 𝓛 L (GLBConj b₀ K₀)).mul_mem
      ((MK 𝓛 L (GLBConj b₀ K₀)).mul_mem (hRq0 k hk) (Zl_le_MK 𝓛 L (GLBConj b₀ K₀) (hzZl k hk)))
      ((MK 𝓛 L (GLBConj b₀ K₀)).inv_mem (hRq1 k hk))
  have hxK₁' : ∀ u ∈ GLBConj b₀ K₀, x⁻¹ * u * x ∈ GLBConj b₀ K₀ := by
    intro u hu
    have h := (Subgroup.mem_normalizer_iff.1
      ((Subgroup.normalizer (GLBConj b₀ K₀ : Set G)).inv_mem hxK₁)) u
    rw [inv_inv] at h
    exact h.1 hu
  have hcentral : ∀ u ∈ GLBConj b₀ K₀, ∀ t ∈ GLBConj b₀ K₀,
      u⁻¹ * (x⁻¹ * u * x) * t = t * (u⁻¹ * (x⁻¹ * u * x)) := by
    intro u hu t ht
    have hk : b₀ * u * b₀⁻¹ ∈ K₀ := mem_gLBConj.1 hu
    have hy := hQ (b₀ * u * b₀⁻¹) hk
    have e0 : cj b₀ (b₀ * u * b₀⁻¹) 1 = u := by
      unfold cj
      rw [pow_one]
      group
    have e1 : cj (b₀ * x) (b₀ * u * b₀⁻¹) 1 = x⁻¹ * u * x := by
      unfold cj
      rw [pow_one]
      group
    rw [e0, e1] at hy
    exact central_of_MK hcp hK₁𝓛 hy t ht
  have hK1c : ∀ a ∈ GLBConj b₀ K₀, ∀ b' ∈ GLBConj b₀ K₀,
      ⁅a, b'⁆ ∈ Subgroup.centralizer ({x} : Set G) := by
    intro a ha b' hb'
    obtain ⟨ca, hca⟩ : ∃ c : G, c = a⁻¹ * (x⁻¹ * a * x) := ⟨_, rfl⟩
    obtain ⟨cb, hcb⟩ : ∃ c : G, c = b'⁻¹ * (x⁻¹ * b' * x) := ⟨_, rfl⟩
    have hca_c : ∀ t ∈ GLBConj b₀ K₀, ca * t = t * ca := fun t ht => by
      rw [hca]; exact hcentral a ha t ht
    have hcb_c : ∀ t ∈ GLBConj b₀ K₀, cb * t = t * cb := fun t ht => by
      rw [hcb]; exact hcentral b' hb' t ht
    have ha' : x⁻¹ * a * x = a * ca := by rw [hca]; group
    have hb'' : x⁻¹ * b' * x = b' * cb := by rw [hcb]; group
    have hcaK : ca ∈ GLBConj b₀ K₀ := by
      rw [hca]
      exact (GLBConj b₀ K₀).mul_mem ((GLBConj b₀ K₀).inv_mem ha) (hxK₁' a ha)
    have hcbK : cb ∈ GLBConj b₀ K₀ := by
      rw [hcb]
      exact (GLBConj b₀ K₀).mul_mem ((GLBConj b₀ K₀).inv_mem hb') (hxK₁' b' hb')
    have key : x⁻¹ * ⁅a, b'⁆ * x = ⁅a, b'⁆ := by
      have e1 : x⁻¹ * ⁅a, b'⁆ * x = ⁅x⁻¹ * a * x, x⁻¹ * b' * x⁆ := by
        simp only [commutatorElement_def]
        group
      rw [e1, ha', hb'',
        comm_mul_right_central (hca_c _ ((GLBConj b₀ K₀).mul_mem hb' hcbK)),
        comm_mul_right_of_comm (hcb_c a ha)]
    have hcomm' : ⁅a, b'⁆ * x = x * ⁅a, b'⁆ := by
      calc ⁅a, b'⁆ * x = x * (x⁻¹ * ⁅a, b'⁆ * x) := by group
        _ = x * ⁅a, b'⁆ := by rw [key]
    exact Subgroup.mem_centralizer_singleton_iff.2 hcomm'
  have hK1le : GLBConj b₀ K₀ ≤ Subgroup.centralizer ({x} : Set G) :=
    qs_le_of_comm (hcp.comp (GLBConj b₀ K₀) hK₁𝓛).2.2 (fun a ha b' hb' => hK1c a ha b' hb')
  have hK1' : ∀ y ∈ GLBConj b₀ K₀, x * y = y * x := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hK1le hy)).symm
  have hK0c : ∀ y ∈ K₀, x * y = y * x :=
    cent_of_conj_comp hcx.inv_left.eq (gLBConj_inv_gLBConj b₀ K₀) hK1'
  have hMc : ∀ M ∈ 𝓛, ∀ y ∈ M, x * y = y * x := by
    intro M hM
    obtain ⟨c, hc, hcM⟩ := hcp.trans K₀ hK₀ M hM
    exact cent_of_conj_comp (inB_comm hcp hc hxB) hcM hK0c
  have hLc : L ≤ Subgroup.centralizer ({x} : Set G) := by
    rw [hcp.gen]
    refine sSup_le fun M hM => ?_
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.2 (hMc M hM y hy).symm
  have hxc : x ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => Subgroup.mem_centralizer_singleton_iff.1 (hLc hh)
  exact hC x hxB hx1 hxc

theorem R1_K₀_le {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {K₀ : Subgroup G} (hK₀ : K₀ ∈ 𝓛) (hpK : p ∣ Nat.card K₀)
    {b₀ : G} (hb₀ : b₀ ∈ B) (hb₀N : b₀ ∉ Subgroup.normalizer (K₀ : Set G))
    (hR1 : ∀ b' ∈ B, ∃ e : ℤ, b' * (b₀ ^ e)⁻¹ ∈ Subgroup.normalizer (K₀ : Set G))
    (hx : ∃ x ∈ B, x ∈ Subgroup.normalizer (K₀ : Set G) ∧ x ≠ 1)
    (hC : ∀ c ∈ B, c ≠ 1 → c ∉ Subgroup.centralizer (L : Set G)) :
    K₀ ≤ Wof p B L K₀ := by
  classical
  obtain ⟨w₀, hmin⟩ := exists_minW hp hcp hK₀ hpK hb₀ hb₀N
  have hsupp_ne : (supp 𝓛 L w₀).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    exact hmin.2.1 (supp_eq_empty_central hcp (Wof_le_L K₀ hmin.1) hemp)
  by_cases htwo : ∃ M₁ ∈ supp 𝓛 L w₀, ∃ M₂ ∈ supp 𝓛 L w₀, M₁ ≠ M₂
  · exfalso
    obtain ⟨M₁, h1, M₂, h2, hne⟩ := htwo
    have hall := r1_two_case hp hcp hK₀ hpK hb₀ hb₀N hR1 hmin h1 h2 hne
    obtain ⟨x, hxB, hxN, hx1⟩ := hx
    exact r1_full_case hp hcp hK₀ hpK hb₀ hb₀N hmin hall hxB hxN hx1 hC
  · push_neg at htwo
    obtain ⟨M, hM⟩ := hsupp_ne
    exact singleton_case hp hcp hK₀ hpK hb₀ hb₀N hmin hM (fun M' hM' => htwo M' hM' M hM)

theorem core_L_le {p : ℕ} (hp : p.Prime) {B L : Subgroup G} {𝓛 : Set (Subgroup G)}
    (hcp : CPData p B L 𝓛) {L₁ : Subgroup G} (hL₁ : L₁ ∈ 𝓛) (hpL : p ∣ Nat.card L)
    (hrank : p ^ 2 ≤ Nat.card B)
    (hJ : ∃ b ∈ B, b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set G) ∨
      b ∉ Subgroup.normalizer (L₁ : Set G))) :
    L ≤ Wof p B L L₁ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpK : p ∣ Nat.card L₁ := hcp.p_dvd_card hp hpL hL₁
  by_cases hA : ∃ b ∈ B, b ≠ 1 ∧ b ∈ Subgroup.centralizer (L : Set G)
  · obtain ⟨b, hb, hb1, hbC⟩ := hA
    exact caseA_le hp hcp hpL hb hb1 hbC
  · push_neg at hA
    obtain ⟨b₀, hb₀, hb₀1, hJ'⟩ := hJ
    have hb₀N : b₀ ∉ Subgroup.normalizer (L₁ : Set G) := hJ'.resolve_left (hA b₀ hb₀ hb₀1)
    by_cases hR2 : ∃ b' ∈ B, b' ∉ Subgroup.normalizer (L₁ : Set G) ∧
        ∀ i j : ℕ, GLBConj (b₀ ^ i) L₁ = GLBConj (b' ^ j) L₁ → p ∣ i
    · obtain ⟨b', hb', hb'N, hind⟩ := hR2
      exact L_le_Wof_of_K₀_le hcp hL₁ (R2_K₀_le hp hcp hL₁ hb₀ hb₀N hb' hb'N hind hpK)
    · have hR1 : ∀ b' ∈ B, ∃ e : ℤ, b' * (b₀ ^ e)⁻¹ ∈ Subgroup.normalizer (L₁ : Set G) := by
        intro b' hb'
        by_cases hb'N : b' ∈ Subgroup.normalizer (L₁ : Set G)
        · exact ⟨0, by simpa using hb'N⟩
        · push_neg at hR2
          obtain ⟨i, j, heq, hpi⟩ := hR2 b' hb' hb'N
          have hu := gLBConj_eq_norm L₁ heq
          have hbp : b₀ ^ p = 1 := hcp.elem.2 b₀ hb₀
          have hb'p : b' ^ p = 1 := hcp.elem.2 b' hb'
          have hi1 : Nat.Coprime i p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpi).symm
          by_cases hpj : p ∣ j
          · have hj1 : b' ^ j = 1 := by
              obtain ⟨m, rfl⟩ := hpj
              rw [pow_mul, hb'p, one_pow]
            rw [hj1, one_mul] at hu
            have hbi : b₀ ^ i ∈ Subgroup.normalizer (L₁ : Set G) := by
              have := (Subgroup.normalizer (L₁ : Set G)).inv_mem hu
              simpa using this
            exact absurd (mem_of_pow_coprime hbp hi1 hbi) hb₀N
          · have hj1 : Nat.Coprime j p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hpj).symm
            obtain ⟨A, hA'⟩ := zpow_gen_of_coprime hb'p hj1
            refine ⟨(i : ℤ) * A, ?_⟩
            have hbiB : b₀ ^ i ∈ B := B.pow_mem hb₀ i
            have hu_B : b' ^ j * (b₀ ^ i)⁻¹ ∈ B :=
              B.mul_mem (B.pow_mem hb' j) (B.inv_mem hbiB)
            have hcomm : Commute (b' ^ j * (b₀ ^ i)⁻¹) (b₀ ^ i) := by
              have := hcp.elem.1.is_comm.comm ⟨_, hu_B⟩ ⟨_, hbiB⟩
              exact congrArg Subtype.val this
            have hsplit : b' = (b' ^ j * (b₀ ^ i)⁻¹) ^ A * (b₀ ^ i) ^ A := by
              rw [← hcomm.mul_zpow, inv_mul_cancel_right, hA']
            have hz : b' * (b₀ ^ ((i : ℤ) * A))⁻¹ = (b' ^ j * (b₀ ^ i)⁻¹) ^ A := by
              rw [zpow_mul, zpow_natCast]
              conv_lhs => rw [hsplit]
              group
            rw [hz]
            exact Subgroup.zpow_mem _ hu A
      have hx := exists_nontriv_N hp hcp hb₀ hb₀1 hR1 hrank
      exact L_le_Wof_of_K₀_le hcp hL₁ (R1_K₀_le hp hcp hL₁ hpK hb₀ hb₀N hR1 hx hA)

end Core

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Input223

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem input22_3_2_holds : Input22_3_2 := by
  intro Y _ _ p hp B L L₁ 𝓛 hB hBN hL₁ hrank hpL hgen hcomp hcomm htrans hJ
  haveI : Fact p.Prime := ⟨hp⟩
  have hcp : Input223.CPData p B L 𝓛 := ⟨hB, hBN, hcomp, hgen, hcomm, htrans⟩
  have hrank' : p ^ 2 ≤ Nat.card B := by
    rw [l1110_card_eq_pow_pRank hB]
    exact Nat.pow_le_pow_right hp.pos hrank
  show L = sSup (Input223.layerSet p B L L₁)
  exact le_antisymm (Input223.core_L_le hp hcp hL₁ hpL hrank' hJ)
    (sSup_le fun Z hZ => by
      obtain ⟨b, hb, hb1, hJb, rfl⟩ := hZ
      exact (Input223.layer_le_self _).trans inf_le_left)

open CFSG.Open
open scoped commutatorElement

theorem input22_3_clause2_holds : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime →
    ∀ (L B K₁ : Subgroup X) (𝒦 : Set (Subgroup X)), K₁ ∈ 𝒦 →
      (∀ K ∈ 𝒦, CFSG.Open.IsComponentOf K L) → L = ⨆ K ∈ 𝒦, K →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ⁅K, K'⁆ = ⊥) →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, ∃ b ∈ B, GLBConj b K = K') →
      CFSG.Open.IsElemAbelian p B → B ≤ Subgroup.normalizer (L : Set X) → p ∣ Nat.card ↥L →
      ((∃ b : X, b ∈ B ∧ b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨
          b ∉ Subgroup.normalizer (K₁ : Set X))) →
        p ^ 2 ≤ Nat.card ↥B →
        L = ⨆ (b : X) (_ : b ∈ B ∧ b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨
            b ∉ Subgroup.normalizer (K₁ : Set X))),
          CFSG.Open.GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X))) := by
  intro X _ _ p hp L B K₁ 𝒦 hK₁ hcomp hL hcomm htrans hB hBN hpL hJ hrank
  haveI : Fact p.Prime := ⟨hp⟩
  have hr2 : 2 ≤ CFSG.Open.pRank p B := by
    rw [l1110_card_eq_pow_pRank hB] at hrank
    exact (Nat.pow_le_pow_iff_right (by have := hp.two_le; omega)).1 hrank
  have hLsup : L = sSup 𝒦 := hL.trans sSup_eq_iSup.symm
  have hcommE : ∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
    intro K hK K' hK' hne x hx y hy
    have hmem : ⁅x, y⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [hcomm K hK K' hK' hne, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hmem
  have key := input22_3_2_holds X p hp B L K₁ 𝒦 hB hBN hK₁ hr2 hpL hLsup hcomp hcommE htrans hJ
  have hS : sSup {Z : Subgroup X | ∃ b ∈ B, b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨
      b ∉ Subgroup.normalizer (K₁ : Set X)) ∧
        Z = CFSG.Open.GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X))} =
      ⨆ (b : X) (_ : b ∈ B ∧ b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨
            b ∉ Subgroup.normalizer (K₁ : Set X))),
        CFSG.Open.GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X)) := by
    apply le_antisymm
    · refine sSup_le fun Z hZ => ?_
      obtain ⟨b, hb, hb1, hbJ, rfl⟩ := hZ
      exact le_iSup₂_of_le b ⟨hb, hb1, hbJ⟩ le_rfl
    · refine iSup₂_le fun b hb => le_sSup ⟨b, hb.1, hb.2.1, hb.2.2, rfl⟩
  exact key.trans hS

theorem sec13e_input22_3_of_clause1 (h1 : ∀ (X : Type) [Group X] [Finite X] (p : ℕ), p.Prime →
    ∀ (L B K₁ : Subgroup X) (𝒦 : Set (Subgroup X)), K₁ ∈ 𝒦 →
      (∀ K ∈ 𝒦, CFSG.Open.IsComponentOf K L) → L = ⨆ K ∈ 𝒦, K →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, K ≠ K' → ⁅K, K'⁆ = ⊥) →
      (∀ K ∈ 𝒦, ∀ K' ∈ 𝒦, ∃ b ∈ B, GLBConj b K = K') →
      CFSG.Open.IsElemAbelian p B → B ≤ Subgroup.normalizer (L : Set X) → p ∣ Nat.card ↥L →
      (∀ b ∈ {b : X | b ∈ B ∧ b ≠ 1 ∧ (b ∈ Subgroup.centralizer (L : Set X) ∨
          b ∉ Subgroup.normalizer (K₁ : Set X))},
        ∀ Y : Subgroup X,
          CFSG.Open.IsComponentOf Y (CFSG.Open.GLAPLayer p (L ⊓ Subgroup.centralizer ({b} : Set X))) →
          ∃ K ∈ 𝒦, ∃ φ : ↥K →* ↥Y, Function.Surjective φ ∧ φ.ker ≤ Subgroup.center ↥K)) :
    Sec13e.Input22_3 := by
  intro X _ _ p hp L B K₁ 𝒦 hK₁ hcomp hL hcomm htrans hB hBN hpL
  exact ⟨h1 X p hp L B K₁ 𝒦 hK₁ hcomp hL hcomm htrans hB hBN hpL,
    input22_3_clause2_holds X p hp L B K₁ 𝒦 hK₁ hcomp hL hcomm htrans hB hBN hpL⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
