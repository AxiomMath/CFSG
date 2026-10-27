module

public import CFSG.ClassicalInvolution.Q3.Sec13StarCex
public import CFSG.ClassicalInvolution.Q3.Sec13StarDich
public import CFSG.ClassicalInvolution.Q3.Sec13StarAE5
public import CFSG.ClassicalInvolution.Q3.Sec13StarCount

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin

variable {G : Type} [Group G] [Finite G]

namespace Third

private theorem add_two_lt_two_pow (n : ℕ) : n + 2 < 2 ^ (n / 2 + 2) := by
  have h1 : n / 2 < 2 ^ (n / 2) := Nat.lt_two_pow_self (n := n / 2)
  have h2 : 2 ^ (n / 2 + 2) = 2 ^ (n / 2) * 4 := by rw [pow_add]; norm_num
  omega

omit [Finite G] in
private theorem le_pCore_of_normal {N : Subgroup G} (hN : N.Normal) (hN2 : IsPGroup 2 N) :
    N ≤ pCore 2 G :=
  le_sSup (s := {K : Subgroup G | K.Normal ∧ IsPGroup 2 K}) ⟨hN, hN2⟩

omit [Finite G] in
private theorem conjSub_le_sup_of_mem {a : G} (ha : a ∈ pCore 2 G) (L : Subgroup G) :
    conjSub a L ≤ pCore 2 G ⊔ L := by
  intro x hx
  rw [mem_conjSub_iff] at hx
  have h1 : x * (a⁻¹ * x * a)⁻¹ ∈ pCore 2 G := by
    have e : x * (a⁻¹ * x * a)⁻¹ = x * a⁻¹ * x⁻¹ * a := by group
    rw [e]
    exact (pCore 2 G).mul_mem (pCore_normal.conj_mem _ ((pCore 2 G).inv_mem ha) x) ha
  have e : x = x * (a⁻¹ * x * a)⁻¹ * (a⁻¹ * x * a) := by group
  rw [e]
  exact Subgroup.mul_mem_sup h1 hx

section Members

variable {Ω : Set (Subgroup G)} (h : StarHyp Ω)
include h

private theorem card_eq_eight {L : Subgroup G} (hL : L ∈ Ω) : Nat.card L = 8 :=
  (h.thmD.card L hL).trans (by norm_num)

private theorem exists_mul_ne {L : Subgroup G} (hL : L ∈ Ω) :
    ∃ x ∈ L, ∃ y ∈ L, x * y ≠ y * x := by
  obtain ⟨P, hPL, hP⟩ := (h.thmD.hyp.omega1 L hL).2
  rw [isMulCommutative_iff] at hP
  push Not at hP
  obtain ⟨x, y, hxy⟩ := hP
  exact ⟨x, hPL.1 x.2, y, hPL.1 y.2, fun e => hxy (Subtype.ext e)⟩

private theorem mem_pCore_of_isUniqueInvolution {L : Subgroup G} (hL : L ∈ Ω) {z : G}
    (hz : IsUniqueInvolution L z) : z ∈ pCore 2 G := by
  obtain ⟨N, hN, hN2, hzN⟩ := h.thmD.inO2 L hL z hz
  exact le_pCore_of_normal hN hN2 hzN

private theorem commutes_of_le_of_isPGroup {L M : Subgroup G} (hL : L ∈ Ω) (hM : M ∈ Ω)
    (hne : L ≠ M) {P : Subgroup G} (hP : IsPGroup 2 P) (hLP : L ≤ P) (hMP : M ≤ P) :
    Commutes L M := by
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  have hR : ∀ {N : Subgroup G}, N ∈ Ω → N ∈ RSet Ω := fun hN =>
    mem_RSet_of_isSylow2In hN ⟨le_rfl, h.thmD.two _ hN, fun _ h1 _ h2 => le_antisymm h1 h2⟩
  exact Q3CP.l67Gen G Ω h.thmD.hyp S' L (hR hL) M (hR hM) (hLP.trans hS') (hMP.trans hS') hne

private theorem orderOf_eq_four_of_mul_ne {L : Subgroup G} (hL : L ∈ Ω) {x : G} (hx : x ∈ L)
    {y : G} (hy : y ∈ L) (hxy : x * y ≠ y * x) : orderOf x = 4 := by
  obtain ⟨z, hz⟩ := (h.thmD.hyp.omega1 L hL).1
  have hdvd : orderOf x ∣ 2 ^ 3 := by
    rw [← h.thmD.card L hL, ← Subgroup.orderOf_mk x hx]
    exact orderOf_dvd_natCard _
  obtain ⟨k, hk, hkx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  interval_cases k
  · rw [pow_zero, orderOf_eq_one_iff] at hkx
    exact absurd (by simp [hkx]) hxy
  · have hxx : x * x = 1 := by
      have e := pow_orderOf_eq_one x
      rwa [hkx, pow_one, pow_two] at e
    rcases hz.unique x hx hxx with rfl | rfl
    · exact absurd (by simp) hxy
    · exact absurd (mul_inv_eq_iff_eq_mul.mp (hz.conj_eq (conjSub_eq_self_of_mem hy))).symm hxy
  · simpa using hkx
  · have heq : Subgroup.zpowers x = L := Subgroup.eq_of_le_of_card_ge
      (Subgroup.zpowers_le.mpr hx) (le_of_eq (by rw [Nat.card_zpowers, hkx, h.thmD.card L hL]))
    rw [← heq] at hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact absurd ((Commute.refl x).zpow_right m).eq hxy

private theorem iSup_le_centralizer {P : Subgroup G} (hP : IsPGroup 2 P)
    {𝓠 : Finset (Subgroup G)} (h𝓠 : ∀ L ∈ 𝓠, L ∈ Ω ∧ L ≤ P) {M : Subgroup G} (hM : M ∈ Ω)
    (hMP : M ≤ P) (hM𝓠 : M ∉ 𝓠) : (⨆ L ∈ 𝓠, L) ≤ Subgroup.centralizer (M : Set G) := by
  refine iSup₂_le fun L hL x hx => Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
  have hne : L ≠ M := fun e => hM𝓠 (e ▸ hL)
  exact (commutes_of_le_of_isPGroup h (h𝓠 L hL).1 hM hne hP (h𝓠 L hL).2 hMP x hx y hy).symm

private theorem mem_centMembers_of_mem_iSup {P : Subgroup G} (hP : IsPGroup 2 P)
    {𝓠 : Finset (Subgroup G)} (h𝓠 : ∀ L ∈ 𝓠, L ∈ Ω ∧ L ≤ P) {M : Subgroup G} (hM : M ∈ Ω)
    (hMP : M ≤ P) (hM𝓠 : M ∉ 𝓠) {a : G} (ha : a ∈ ⨆ L ∈ 𝓠, L) :
    M ∈ Generic.centMembers Ω a :=
  Generic.mem_centMembers_iff_commute.mpr ⟨hM, fun k hk =>
    Subgroup.mem_centralizer_iff.mp (iSup_le_centralizer h hP h𝓠 hM hMP hM𝓠 ha) k hk⟩

end Members

section Steps

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {t : G} {S : Sylow 2 G}
  (c : StarCex Ω K J t S)
include c

private theorem ne_conjSub : K ≠ conjSub t K :=
  (c.conjSub_ne (c.hyp.mem_dstarComp_self c.hK)).symm

private theorem conjSub_mem_others {L : Subgroup G}
    (hL : L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K) :
    conjSub t L ∈ Ω ∧ conjSub t L ≤ (S : Subgroup G) ∧ conjSub t L ≠ K ∧
      conjSub t L ≠ conjSub t K := by
  obtain ⟨hLΩ, hLS, hLK, hLK'⟩ := hL
  refine ⟨c.hyp.thmD.hyp.conjInvariant t L hLΩ, c.conjSub_le hLS, fun e => hLK' ?_,
    fun e => hLK (conjSub_injective t e)⟩
  rw [← e, ← conjSub_mul, c.ht.sq, conjSub_one]

private theorem two_pow_le_card_others {𝓟 : Finset (Subgroup G)}
    (h𝓟 : ∀ L, L ∈ 𝓟 ↔ L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K)
    (hne : 𝓟.Nonempty) :
    2 ^ (𝓟.card / 2 + 2) ≤ Nat.card ↥((⨆ L ∈ 𝓟, L) ⊓ pCore 2 G) := by
  have h := c.hyp
  have hm : ∀ L ∈ 𝓟, L ∈ Ω ∧ L ≤ (S : Subgroup G) := fun L hL =>
    ⟨((h𝓟 L).1 hL).1, ((h𝓟 L).1 hL).2.1⟩
  refine two_pow_le_card_iSup_inf pCore_normal (mem_pCore_of_isUniqueInvolution h c.hJ c.ht)
    c.ht.sq 𝓟 (fun L hL => card_eq_eight h (hm L hL).1)
    (fun L hL => exists_mul_ne h (hm L hL).1) (fun L hL => ?_)
    (fun L hL L' hL' hLL' => commutes_of_le_of_isPGroup h (hm L hL).1 (hm L' hL').1 hLL'
      S.isPGroup' (hm L hL).2 (hm L' hL').2)
    (fun L hL => (h𝓟 _).2 (conjSub_mem_others c ((h𝓟 L).1 hL)))
    (fun L hL => c.conjSub_ne (c.mem_dstarComp_of_le (hm L hL).1 (hm L hL).2)) hne
  obtain ⟨z, hz⟩ := (h.thmD.hyp.omega1 L (hm L hL).1).1
  exact ⟨z, hz, mem_pCore_of_isUniqueInvolution h (hm L hL).1 hz⟩

private theorem forall_mem_dstarComp {K₁ M₁ : Subgroup G}
    (hK₁ : K₁ ∈ Ω) (hK₁S : K₁ ≤ (S : Subgroup G)) (hK₁K : K₁ ≠ K) (hK₁t : K₁ ≠ conjSub t K)
    (hM₁ : ∀ x ∈ K₁, ∀ y ∈ M₁, x * y = y * x) {a : G} (ha : a ≠ 1) (haM : a ∈ K₁ ⊔ M₁)
    (haK : K ∈ Generic.centMembers Ω a) (haK' : conjSub t K ∈ Generic.centMembers Ω a) :
    ∀ L ∈ Generic.centMembers Ω a, L ∈ dstarComp Ω K := by
  have h := c.hyp
  have hK' : conjSub t K ∈ Ω := h.thmD.hyp.conjInvariant t K c.hK
  have hK'S : conjSub t K ≤ (S : Subgroup G) := c.conjSub_le c.hKS
  have hcomm : ∀ {L M : Subgroup G}, L ∈ Ω → M ∈ Ω → L ≠ M → L ≤ (S : Subgroup G) →
      M ≤ (S : Subgroup G) → Commutes L M := fun hL hM hne hLS hMS =>
    commutes_of_le_of_isPGroup h hL hM hne S.isPGroup' hLS hMS
  have cKK' := hcomm c.hK hK' (ne_conjSub c) c.hKS hK'S
  rcases h.centMembers_dichotomy ha haK with hall | hI
  · exact hall
  obtain ⟨I⟩ := hI
  by_cases hK₁a : K₁ ∈ Generic.centMembers Ω a
  · exact (h.false_of_aeIdent_three (fun L hL => (Generic.mem_centMembers.mp hL).1) I haK haK'
      hK₁a (ne_conjSub c) hK₁K.symm hK₁t.symm cKK' (hcomm c.hK hK₁ hK₁K.symm c.hKS hK₁S)
      (hcomm hK' hK₁ hK₁t.symm hK'S hK₁S)).elim
  obtain ⟨x, hx, hxa⟩ := exists_inner_of_mem_sup hM₁ haM
  have hxa' : x * a = a * x := by
    have e := hxa x hx
    rw [mul_inv_cancel_right x x] at e
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  obtain ⟨y, hy, hxy⟩ : ∃ y ∈ K₁, x * y ≠ y * x := by
    by_contra hcon
    push Not at hcon
    refine hK₁a (Generic.mem_centMembers_iff_commute.mpr ⟨hK₁, fun y hy => ?_⟩)
    have e := hxa y hy
    rw [hcon y hy, mul_inv_cancel_right y x] at e
    exact (mul_inv_eq_iff_eq_mul.mp e).symm
  have hall := h.mem_dstarComp_of_aeIdent I haK haK' (ne_conjSub c) cKK' hK₁ hx hxa'
    (orderOf_eq_four_of_mul_ne h hK₁ hx hy hxy) (hcomm hK₁ c.hK hK₁K hK₁S c.hKS x hx)
    (hcomm hK₁ hK' hK₁t hK₁S hK'S x hx)
  exact fun L hL => h.mem_dstarComp_trans (c.mem_dstarComp_of_le hK₁ hK₁S) (hall L hL)

private theorem conjSub_ne_of_forall {a : G} (haQ : a ∈ pCore 2 G)
    (haK : K ∈ Generic.centMembers Ω a)
    (hSig : ∀ L ∈ Generic.centMembers Ω a, L ∈ dstarComp Ω K) : conjSub a J ≠ J := by
  intro haJ
  have h := c.hyp
  have hact : ∀ y ∈ J, a * y * a⁻¹ = y ∨ a * y * a⁻¹ = y * t := by
    intro y hy
    have hyJ : a * y * a⁻¹ ∈ J := by
      rw [← haJ]
      exact conj_mem_conjSub hy
    have hcQ : a * y * a⁻¹ * y⁻¹ ∈ pCore 2 G := by
      have e : a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) := by group
      rw [e]
      exact (pCore 2 G).mul_mem haQ (pCore_normal.conj_mem _ ((pCore 2 G).inv_mem haQ) y)
    rcases h.eq_one_or_eq_of_mem_pCore c.hJ c.hK c.hJK c.ht (J.mul_mem hyJ (J.inv_mem hy)) hcQ
      with e | e
    · exact Or.inl (mul_inv_eq_one.mp e)
    · refine Or.inr ((mul_inv_eq_iff_eq_mul.mp e).trans ?_)
      exact (mul_inv_eq_iff_eq_mul.mp (c.ht.conj_eq (conjSub_eq_self_of_mem hy))).symm
  obtain ⟨u, huJ, hu4, hau⟩ :=
    exists_comm_orderOf_four c.ht (card_eq_eight h c.hJ) (exists_mul_ne h c.hJ) hact
  have huK : conjSub u K ∈ Generic.centMembers Ω a := by
    have hu := Generic.conjSub_mem_centMembers h.thmD.hyp.conjInvariant (n := u) haK
    rwa [← hau, mul_inv_cancel_right a u] at hu
  exact h.not_mem_compStab c.hK c.hJ c.hJK huJ hu4 ((h.mem_compStab_iff c.hK).mpr (hSig _ huK))

private theorem eq_one_of_conjSub_eq {𝓟 : Finset (Subgroup G)}
    (h𝓟 : ∀ L, L ∈ 𝓟 ↔ L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K)
    {K₁ : Subgroup G} (hK₁ : K₁ ∈ 𝓟) {a : G} (ha : a ∈ (⨆ L ∈ 𝓟, L) ⊓ pCore 2 G)
    (haJ : conjSub a J = J) : a = 1 := by
  classical
  have h := c.hyp
  by_contra ha1
  obtain ⟨haM, haQ⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hK₁Ω, hK₁S, hK₁K, hK₁t⟩ := (h𝓟 K₁).1 hK₁
  have hm : ∀ L ∈ 𝓟, L ∈ Ω ∧ L ≤ (S : Subgroup G) := fun L hL =>
    ⟨((h𝓟 L).1 hL).1, ((h𝓟 L).1 hL).2.1⟩
  have haK : K ∈ Generic.centMembers Ω a :=
    mem_centMembers_of_mem_iSup h S.isPGroup' hm c.hK c.hKS (fun hK => ((h𝓟 K).1 hK).2.2.1 rfl)
      haM
  have haK' : conjSub t K ∈ Generic.centMembers Ω a :=
    mem_centMembers_of_mem_iSup h S.isPGroup' hm (h.thmD.hyp.conjInvariant t K c.hK)
      (c.conjSub_le c.hKS) (fun hK => ((h𝓟 _).1 hK).2.2.2 rfl) haM
  have hM₁ : ∀ x ∈ K₁, ∀ y ∈ ⨆ L ∈ 𝓟.erase K₁, L, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (iSup_le_centralizer h S.isPGroup'
      (fun L hL => hm L (Finset.mem_of_mem_erase hL)) hK₁Ω hK₁S (Finset.notMem_erase K₁ 𝓟) hy)
      x hx
  have hle : (⨆ L ∈ 𝓟, L) ≤ K₁ ⊔ ⨆ L ∈ 𝓟.erase K₁, L := by
    refine iSup₂_le fun L hL => ?_
    by_cases hLK₁ : L = K₁
    · rw [hLK₁]
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le L (Finset.mem_erase.mpr ⟨hLK₁, hL⟩) le_rfl)
  exact conjSub_ne_of_forall c haQ haK
    (forall_mem_dstarComp c hK₁Ω hK₁S hK₁K hK₁t hM₁ ha1 (hle haM) haK haK') haJ

private theorem card_le_card_add_two {𝓟 : Finset (Subgroup G)}
    (h𝓟 : ∀ L, L ∈ 𝓟 ↔ L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K)
    {A : Subgroup G} (hA : A ≤ pCore 2 G) (hfree : ∀ a ∈ A, conjSub a J = J → a = 1) :
    Nat.card A ≤ 𝓟.card + 2 := by
  classical
  have h := c.hyp
  have hP : IsPGroup 2 ↥(pCore 2 G ⊔ J) :=
    pCore_isPGroup.to_sup_of_normal_left (h.thmD.two J c.hJ)
  obtain ⟨S', hS'⟩ := hP.exists_le_sylow
  have h1 : Nat.card A ≤ {L | L ∈ Ω ∧ L ≤ (S' : Subgroup G)}.ncard :=
    card_le_ncard_of_free (Set.toFinite _) (fun a ha =>
      ⟨h.thmD.hyp.conjInvariant a J c.hJ, (conjSub_le_sup_of_mem (hA ha) J).trans hS'⟩) hfree
  rw [← ncard_le_sylow_eq h.thmD.hyp.conjInvariant S S'] at h1
  have h2 : {L | L ∈ Ω ∧ L ≤ (S : Subgroup G)} ⊆
      ↑(insert K (insert (conjSub t K) 𝓟)) := by
    intro L hL
    by_cases hLK : L = K
    · simp [hLK]
    by_cases hLK' : L = conjSub t K
    · simp [hLK']
    simp [(h𝓟 L).2 ⟨hL.1, hL.2, hLK, hLK'⟩]
  have h3 := Set.ncard_le_ncard h2 (Finset.finite_toSet _)
  rw [Set.ncard_coe_finset] at h3
  have h4 := Finset.card_insert_le K (insert (conjSub t K) 𝓟)
  have h5 := Finset.card_insert_le (conjSub t K) 𝓟
  omega

end Steps

end Third

namespace StarCex

variable {Ω : Set (Subgroup G)} {K J : Subgroup G} {t : G} {S : Sylow 2 G}
  (c : StarCex Ω K J t S)
include c

theorem false_of_third {K₁ : Subgroup G} (hK₁ : K₁ ∈ Ω)
    (hK₁S : K₁ ≤ (S : Subgroup G)) (hK₁K : K₁ ≠ K) (hK₁t : K₁ ≠ conjSub t K) : False := by
  obtain ⟨𝓟, h𝓟⟩ : ∃ 𝓟 : Finset (Subgroup G), ∀ L, L ∈ 𝓟 ↔
      L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K :=
    ⟨(Set.toFinite {L | L ∈ Ω ∧ L ≤ (S : Subgroup G) ∧ L ≠ K ∧ L ≠ conjSub t K}).toFinset,
      fun L => Set.Finite.mem_toFinset _⟩
  have hK₁𝓟 : K₁ ∈ 𝓟 := (h𝓟 K₁).2 ⟨hK₁, hK₁S, hK₁K, hK₁t⟩
  have hlow := Third.two_pow_le_card_others c h𝓟 ⟨K₁, hK₁𝓟⟩
  have hup := Third.card_le_card_add_two c h𝓟 (A := (⨆ L ∈ 𝓟, L) ⊓ pCore 2 G) inf_le_right
    fun a ha haJ => Third.eq_one_of_conjSub_eq c h𝓟 hK₁𝓟 ha haJ
  exact lt_irrefl _ ((Third.add_two_lt_two_pow 𝓟.card).trans_le (hlow.trans hup))

end StarCex

end CFSG.ClassicalInvolution.Q3.Sec13
