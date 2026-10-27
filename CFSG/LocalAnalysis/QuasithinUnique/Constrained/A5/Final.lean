module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Aut6
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique.DoubleA3
open scoped MatrixGroups

section Tools

theorem sq_mem_frattini {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P) (x : P) :
    x ^ 2 ∈ frattini P := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  unfold frattini Order.radical
  rw [Subgroup.mem_iInf]
  intro N
  rw [Subgroup.mem_iInf]
  intro hN
  have hcoat : IsCoatom N := hN
  have hnorm : N.Normal := by
    have hlt : N < ⊤ := lt_top_iff_ne_top.mpr hcoat.1
    have h2 := Group.normalizerCondition_of_isNilpotent N hlt
    have h3 : Subgroup.normalizer (N : Set P) = ⊤ := hcoat.2 _ h2
    exact Subgroup.normalizer_eq_top_iff.1 h3
  by_cases hx : x ∈ N
  · exact N.pow_mem hx 2
  · by_contra hx2
    have hlt : N < N ⊔ Subgroup.zpowers (x ^ 2) := by
      refine lt_of_le_of_ne le_sup_left fun h => hx2 ?_
      have : x ^ 2 ∈ N ⊔ Subgroup.zpowers (x ^ 2) :=
        Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
      rwa [← h] at this
    have htop : N ⊔ Subgroup.zpowers (x ^ 2) = ⊤ := hcoat.2 _ hlt
    have hxmem : x ∈ N ⊔ Subgroup.zpowers (x ^ 2) := htop ▸ Subgroup.mem_top x
    obtain ⟨n, hn, y, hy, hny⟩ := Subgroup.mem_sup_of_normal_left.1 hxmem
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 hP) x
    have hcop : IsCoprime (1 - 2 * k) (2 ^ e : ℤ) := by
      have h2 : IsCoprime (1 - 2 * k) (2 : ℤ) := ⟨1, k, by ring⟩
      exact h2.pow_right
    obtain ⟨s, t, hst⟩ := hcop
    have hxn : x ^ (1 - 2 * k) ∈ N := by
      have h3 : n = x * ((x ^ 2) ^ k)⁻¹ := eq_mul_inv_of_mul_eq hny
      have h4 : x ^ (1 - 2 * k) = x * ((x ^ 2) ^ k)⁻¹ := by
        rw [show (1 - 2 * k : ℤ) = 1 + 2 * (-k) by ring, zpow_add, zpow_mul, zpow_one,
          zpow_neg]
        norm_cast
      rw [h4, ← h3]; exact hn
    have hxN : x ∈ N := by
      have hxo : x ^ ((2 ^ e : ℕ) : ℤ) = 1 := by
        rw [zpow_natCast, ← he]; exact pow_orderOf_eq_one x
      have : x = (x ^ (1 - 2 * k)) ^ s := by
        calc x = x ^ (1 : ℤ) := (zpow_one x).symm
          _ = x ^ ((1 - 2 * k) * s + ((2 ^ e : ℕ) : ℤ) * t) := by
            congr 1; push_cast; linarith [hst]
          _ = (x ^ (1 - 2 * k)) ^ s := by
            rw [zpow_add, zpow_mul, zpow_mul, hxo, one_zpow, mul_one]
      rw [this]
      exact N.zpow_mem hxn s
    exact hx hxN

variable {G : Type*} [Group G]

theorem sq_mem_frattiniOf [Finite G] {S : Subgroup G} (hS : IsPGroup 2 S) {x : G} (hx : x ∈ S) :
    x ^ 2 ∈ frattiniOf S :=
  ⟨(⟨x, hx⟩ : S) ^ 2, sq_mem_frattini hS _, by simp⟩

theorem mul_mem_of_index_two_of_not_mem {T S : Subgroup G} (hidx : S.relIndex T = 2) {x y : G}
    (hx : x ∈ T) (hy : y ∈ T) (hxS : x ∉ S) (hyS : y ∉ S) : x⁻¹ * y ∈ S := by
  have h2 : (S.subgroupOf T).index = 2 := hidx
  have key := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨x⁻¹, T.inv_mem hx⟩ : T))
    (b := (⟨y, hy⟩ : T)))
  have h1 : (⟨x⁻¹, T.inv_mem hx⟩ : T) ∉ S.subgroupOf T := by
    intro h
    exact hxS (by simpa using S.inv_mem (Subgroup.mem_subgroupOf.1 h))
  have h3 : (⟨y, hy⟩ : T) ∉ S.subgroupOf T := fun h => hyS (Subgroup.mem_subgroupOf.1 h)
  have : (⟨x⁻¹, T.inv_mem hx⟩ : T) * ⟨y, hy⟩ ∈ S.subgroupOf T := key.2 (iff_of_false h1 h3)
  exact Subgroup.mem_subgroupOf.1 this

theorem commutator_le_of_index_two {T S : Subgroup G} (hidx : S.relIndex T = 2) : ⁅T, T⁆ ≤ S := by
  have h2 : (S.subgroupOf T).index = 2 := hidx
  have hnorm : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  have hcard : Nat.card (T ⧸ S.subgroupOf T) = 2 := by rw [← Subgroup.index_eq_card]; exact h2
  have : IsCyclic (T ⧸ S.subgroupOf T) := isCyclic_of_prime_card hcard
  have hcomm : IsMulCommutative (T ⧸ S.subgroupOf T) := inferInstance
  have hle :=
    (Subgroup.Normal.quotient_commutative_iff_commutator_le (N := S.subgroupOf T)).1 hcomm
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hmem : ((⟨x, hx⟩ : T) * ⟨y, hy⟩ * (⟨x, hx⟩ : T)⁻¹ * (⟨y, hy⟩ : T)⁻¹ : T) ∈
      commutator T := by
    rw [commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have := Subgroup.mem_subgroupOf.1 (hle hmem)
  simpa [commutatorElement_def] using this

theorem exists_conj_sq_mem_sdiff [Finite G] (hperf : commutator G = ⊤) {T S : Subgroup G}
    (hT : Nat.Coprime 2 T.index) (hST : S ≤ T) (hidx : S.relIndex T = 2) {j z : G} (hjT : j ∈ T)
    (hjS : j ∉ S) (hj2 : j ^ 2 = z) (hz2 : z ^ 2 = 1) (hzS : z ∈ S)
    (hconj : ∀ g : G, g⁻¹ * j * g ∉ S) :
    ∃ g : G, g⁻¹ * z * g ∈ T ∧ g⁻¹ * z * g ∉ S := by
  by_contra hcon
  have hcon' : ∀ g : G, g⁻¹ * z * g ∈ T → g⁻¹ * z * g ∈ S := by
    intro g hg
    by_contra hgS
    exact hcon ⟨g, hg, hgS⟩
  have h2 : (S.subgroupOf T).index = 2 := hidx
  have hnorm : (S.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two h2
  have habel : ⁅T, T⁆ ≤ S := commutator_le_of_index_two hidx
  have hj4 : j ^ 4 = 1 := by
    have : j ^ 4 = (j ^ 2) ^ 2 := by rw [← pow_mul]
    rw [this, hj2, hz2]
  have hj4' : j ^ (4 : ℤ) = 1 := by exact_mod_cast hj4
  have hj8 : j ^ 8 = 1 := by
    have : j ^ 8 = (j ^ 4) ^ 2 := by rw [← pow_mul]
    rw [this, hj4]; simp
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot := generalized_thompson_transfer_one (p := 2) hT ⟨hST, hnorm⟩ habel hjT hjS
    ⟨2, by simpa using hj4⟩
  apply hnot ?_ (hperf ▸ Subgroup.mem_top j)
  intro m a ha
  have hm : j ^ m = j ^ (m % 4) := by
    have hm4 : m = 4 * (m / 4) + m % 4 := by omega
    conv_lhs => rw [hm4]
    rw [zpow_add, zpow_mul, hj4', one_zpow, one_mul]
  have hr : m % 4 = 0 ∨ m % 4 = 1 ∨ m % 4 = 2 ∨ m % 4 = 3 := by omega
  rw [hm] at ha ⊢
  rcases hr with hr | hr | hr | hr
  · rw [hr]; simp
  · rw [hr] at ha ⊢
    simp only [zpow_one] at ha ⊢
    exact mul_mem_of_index_two_of_not_mem hidx hjT ha hjS (hconj a)
  · rw [hr] at ha ⊢
    have hz : j ^ (2 : ℤ) = z := by exact_mod_cast hj2
    rw [hz] at ha ⊢
    have := hcon' a ha
    exact S.mul_mem (S.inv_mem hzS) this
  · rw [hr] at ha ⊢
    have h3 : j ^ (3 : ℤ) = j ^ 3 := by exact_mod_cast rfl
    rw [h3] at ha ⊢
    have hj3T : j ^ 3 ∈ T := T.pow_mem hjT 3
    have hj3S : j ^ 3 ∉ S := by
      intro h
      apply hjS
      have : j = (j ^ 3) * (j ^ 2)⁻¹ := by group
      rw [this, hj2]
      exact S.mul_mem h (S.inv_mem hzS)
    have hynS : a⁻¹ * j ^ 3 * a ∉ S := by
      intro h
      apply hconj a
      have h9 : (a⁻¹ * j ^ 3 * a) ^ 3 ∈ S := S.pow_mem h 3
      have : (a⁻¹ * j ^ 3 * a) ^ 3 = a⁻¹ * j * a := by
        have e1 : (a⁻¹ * j ^ 3 * a) ^ 3 = a⁻¹ * (j ^ 3) ^ 3 * a := by
          have := conj_pow (a := a⁻¹) (b := j ^ 3) (i := 3)
          simpa using this
        rw [e1, ← pow_mul]
        have : j ^ (3 * 3) = j := by
          have : j ^ (3 * 3) = j ^ 8 * j := by rw [← pow_succ]
          rw [this, hj8, one_mul]
        rw [this]
      rwa [this] at h9
    exact mul_mem_of_index_two_of_not_mem hidx hj3T ha hj3S hynS

theorem commutator_eq_top_of_simple [IsSimpleGroup G] (hnc : ∃ a b : G, a * b ≠ b * a) :
    commutator G = ⊤ := by
  rcases (inferInstance : (commutator G).Normal).eq_bot_or_eq_top with h | h
  · exfalso
    have hc : IsMulCommutative G := (commutator_eq_bot_iff G).1 h
    obtain ⟨a, b, hab⟩ := hnc
    exact hab (Std.Commutative.comm a b)
  · exact h

theorem eq_one_or_eq_of_mem_zpowers {z : G} (hz : orderOf z = 2) {w : G}
    (hw : w ∈ Subgroup.zpowers z) : w = 1 ∨ w = z := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
  have h := zpow_mod_orderOf z k
  rw [hz] at h
  have hk : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rcases hk with hk | hk
  · left; rw [← h, hk]; simp
  · right; rw [← h, hk]; simp

theorem zpowers_card_two_facts {z : G} (h : Nat.card (Subgroup.zpowers z) = 2) :
    z ≠ 1 ∧ z ^ 2 = 1 ∧ orderOf z = 2 := by
  have h2 : orderOf z = 2 := by rw [← Nat.card_zpowers]; exact h
  exact ⟨fun h1 => by rw [h1, orderOf_one] at h2; omega, by rw [← h2]; exact pow_orderOf_eq_one z,
    h2⟩

end Tools

section Induces

variable {G : Type*} [Group G] {K : Subgroup G}

theorem inducesPerm_of_mem (e : ↥K ≃* alternatingGroup (Fin 6)) (k₀ : K) :
    InducesPerm e (k₀ : G) ((e k₀ : alternatingGroup (Fin 6)) : Equiv.Perm (Fin 6)) := by
  intro k k' hk
  have : k' = k₀⁻¹ * k * k₀ := Subtype.ext (by simpa using hk)
  rw [this]
  simp [map_mul, map_inv]

theorem InducesPerm.mul' {e : ↥K ≃* alternatingGroup (Fin 6)} {g₁ g₂ : G}
    {σ₁ σ₂ : Equiv.Perm (Fin 6)} (h₁ : InducesPerm e g₁ σ₁) (h₂ : InducesPerm e g₂ σ₂)
    (hg₁ : g₁ ∈ Subgroup.normalizer (K : Set G)) : InducesPerm e (g₁ * g₂) (σ₁ * σ₂) := by
  intro k k' hk
  have hk₁ : g₁⁻¹ * (k : G) * g₁ ∈ K := (Subgroup.mem_set_normalizer_iff''.1 hg₁ k).1 k.2
  have h1 := h₁ k ⟨g₁⁻¹ * (k : G) * g₁, hk₁⟩ rfl
  have h2 := h₂ ⟨g₁⁻¹ * (k : G) * g₁, hk₁⟩ k' (by rw [hk]; group)
  rw [h2, h1]
  group

end Induces

section Main

variable {G : Type} [Group G] {T M H S L : Subgroup G} {z u : G} {K : Subgroup G}

theorem A5Step10.mem_M_of_commute (s : A5Step10 T M H S L z u K) {y : G} (h : z * y = y * z) :
    y ∈ M := by
  have : y ∈ Subgroup.centralizer (centerOf (borelP M L) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    have hw' : w ∈ Subgroup.zpowers z := by rw [← s.z_gen]; exact hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw'
    exact (Commute.zpow_left (show Commute z y from h) k).eq
  rwa [← s.M_cent] at this

theorem A5Step10.conj_mem_P (s : A5Step10 T M H S L z u K) (hu2 : u ^ 2 = 1) (hz1 : z ≠ 1)
    (hz2 : orderOf z = 2) {g : G} (hg : g⁻¹ * z * g ∈ borelP M L) : g⁻¹ * z * g = z := by
  by_contra hne
  have hz2' : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
  have hw2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    have := conj_pow (a := g⁻¹) (b := z) (i := 2)
    simpa [hz2'] using this
  have hw1 : g⁻¹ * z * g ≠ 1 := by
    intro h
    apply hz1
    have : z = g * (g⁻¹ * z * g) * g⁻¹ := by group
    rw [this, h]; simp
  have hwZ : g⁻¹ * z * g ∉ centerOf (borelP M L) := by
    intro hmem
    rw [s.z_gen] at hmem
    rcases eq_one_or_eq_of_mem_zpowers hz2 hmem with h | h
    · exact hw1 h
    · exact hne h
  obtain ⟨m, -, hmw⟩ := s.trans_P _ hg u s.u_mem_P hwZ s.u_not hw2 hu2
  exact s.u_not_conj (g * m) (by rw [← hmw]; group)

theorem A5Step10.case1_false (s : A5Step10 T M H S L z u K) (hu2 : u ^ 2 = 1) (hz1 : z ≠ 1)
    (hz2 : orderOf z = 2) (hPS : borelP M L ≤ S) {g : G} (hiS : g⁻¹ * z * g ∉ S)
    (Y : Subgroup G) (c : G) (hYc : IsTwoThree Y c)
    (hY : Y ≤ Subgroup.centralizer ({g⁻¹ * z * g} : Set G))
    (hc : c ∈ Subgroup.centralizer ({g⁻¹ * z * g} : Set G)) (hzY : z ∈ Y) : False := by
  set J : Subgroup G := Y.map (MulAut.conj g).toMonoidHom with hJ
  have hconjM : ∀ x ∈ Subgroup.centralizer ({g⁻¹ * z * g} : Set G), g * x * g⁻¹ ∈ M := by
    intro x hx
    apply s.mem_M_of_commute
    have hx' := Subgroup.mem_centralizer_iff.1 hx (g⁻¹ * z * g) (Set.mem_singleton _)
    show z * (g * x * g⁻¹) = (g * x * g⁻¹) * z
    calc z * (g * x * g⁻¹) = g * ((g⁻¹ * z * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * z * g)) * g⁻¹ := by rw [hx']
      _ = (g * x * g⁻¹) * z := by group
  have hJM : J ≤ M := by
    rintro _ ⟨x, hx, rfl⟩
    exact hconjM x (hY hx)
  have hcore := s.sl23_core J (g * c * g⁻¹) (hYc.map_conj g) hJM (hconjM c hc)
  have hzJ : g * z * g⁻¹ ∈ J := ⟨z, hzY, by simp [MulAut.conj_apply]⟩
  have hP : g * z * g⁻¹ ∈ borelP M L := by
    rw [← s.P_core]; exact hcore hzJ
  have hP' : (g⁻¹)⁻¹ * z * g⁻¹ ∈ borelP M L := by simpa using hP
  have hzg := s.conj_mem_P hu2 hz1 hz2 hP'
  have hzg' : g * z * g⁻¹ = z := by simpa using hzg
  apply hiS
  have hcomm : g * z = z * g := by
    calc g * z = (g * z * g⁻¹) * g := by group
      _ = z * g := by rw [hzg']
  have : g⁻¹ * z * g = z := by
    calc g⁻¹ * z * g = g⁻¹ * (z * g) := by group
      _ = g⁻¹ * (g * z) := by rw [hcomm]
      _ = z := by group
  rw [this]
  have hzZ : z ∈ centerOf (borelP M L) := by rw [s.z_gen]; exact Subgroup.mem_zpowers z
  exact hPS hzZ.1

theorem A5Step10.case2_false
    [Finite G] (s : A5Step10 T M H S L z u K) (hST : S ≤ T) {i : G}
    (hiT : i ∈ T ⊓ centralizerElem u) (hi2 : i ^ 2 = 1) (hiS : i ∉ S) {h : G}
    (hih : i = h⁻¹ * z * h) : False := by
  obtain ⟨e, ⟨v, hvR, -, -, τ, hτ, hvτ⟩, -⟩ := s.S6
  have hRC : baum S ≤ centralizerElem u := by rw [← s.Su]; exact inf_le_right
  have hRS : baum S ≤ S := by rw [← s.Su]; exact inf_le_left
  have hKC : K ≤ centralizerElem u := s.K_comp.1
  have hnormK : centralizerElem u ≤ Subgroup.normalizer (K : Set G) := s.K_norm
  have hiu : i ∈ centralizerElem u := hiT.2
  have hiT' : i ∈ T := hiT.1
  have hi_norm : i ∈ Subgroup.normalizer (K : Set G) := hnormK hiu
  have hnK : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ k : K, g⁻¹ * (k : G) * g ∈ K :=
    fun g hg k => (Subgroup.mem_set_normalizer_iff''.1 hg k).1 k.2
  have hii : i * i = 1 := by rw [← pow_two]; exact hi2
  let c : ↥K ≃* ↥K :=
    { toFun := fun k => ⟨i⁻¹ * (k : G) * i, hnK i hi_norm k⟩
      invFun := fun k => ⟨i⁻¹ * (k : G) * i, hnK i hi_norm k⟩
      left_inv := fun k => Subtype.ext (by
        show i⁻¹ * (i⁻¹ * (k : G) * i) * i = k
        calc i⁻¹ * (i⁻¹ * (k : G) * i) * i = (i * i)⁻¹ * (k : G) * (i * i) := by group
          _ = k := by rw [hii]; simp)
      right_inv := fun k => Subtype.ext (by
        show i⁻¹ * (i⁻¹ * (k : G) * i) * i = k
        calc i⁻¹ * (i⁻¹ * (k : G) * i) * i = (i * i)⁻¹ * (k : G) * (i * i) := by group
          _ = k := by rw [hii]; simp)
      map_mul' := fun a b => Subtype.ext (by
        show i⁻¹ * ((a : G) * b) * i = (i⁻¹ * a * i) * (i⁻¹ * b * i)
        group) }
  have hcc : ∀ k : K, c (c k) = k := fun k => c.symm_apply_apply k
  have hι : ∀ a : Aut6.A6, (e.symm.trans (c.trans e)) ((e.symm.trans (c.trans e)) a) = a := by
    intro a
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hcc, MulEquiv.apply_symm_apply]
  have hnoσ : ¬ ∃ σ : Equiv.Perm (Fin 6), InducesPerm e i σ := by
    rintro ⟨σ, hσ⟩
    obtain ⟨k0, r, hr, hq⟩ : ∃ (k0 : K) (r : G), r ∈ baum S ∧
        InducesPerm e ((k0 : G) * r) σ := by
      by_cases hσA : σ ∈ alternatingGroup (Fin 6)
      · refine ⟨e.symm ⟨σ, hσA⟩, 1, one_mem _, ?_⟩
        have := inducesPerm_of_mem e (e.symm ⟨σ, hσA⟩)
        simpa using this
      · have hτs : Equiv.Perm.sign τ = -1 := by
          obtain ⟨x, y, hxy, rfl⟩ := hτ
          exact Equiv.Perm.sign_swap hxy
        have hσs : Equiv.Perm.sign σ = -1 := by
          rw [Equiv.Perm.mem_alternatingGroup] at hσA
          exact Int.units_ne_iff_eq_neg.1 hσA
        have hσ' : σ * τ⁻¹ ∈ alternatingGroup (Fin 6) := by
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_inv, hσs, hτs]
          decide
        refine ⟨e.symm ⟨σ * τ⁻¹, hσ'⟩, v, hvR, ?_⟩
        have h1 := inducesPerm_of_mem e (e.symm ⟨σ * τ⁻¹, hσ'⟩)
        have h2 := InducesPerm.mul' h1 hvτ (Subgroup.le_normalizer (e.symm ⟨σ * τ⁻¹, hσ'⟩).2)
        simpa using h2
    have hqC : (k0 : G) * r ∈ centralizerElem u := (centralizerElem u).mul_mem (hKC k0.2) (hRC hr)
    have hqnorm : (k0 : G) * r ∈ Subgroup.normalizer (K : Set G) :=
      hnormK hqC
    set q : G := (k0 : G) * r with hqdef
    have hxK : ∀ k : K, (k : G) * (i * q⁻¹) = (i * q⁻¹) * (k : G) := by
      intro k
      let k₁ : K := ⟨i⁻¹ * (k : G) * i, hnK i hi_norm k⟩
      let k₂ : K := ⟨q⁻¹ * (k : G) * q, hnK q hqnorm k⟩
      have e1 := hσ k k₁ rfl
      have e2 := hq k k₂ rfl
      have hk12 : k₁ = k₂ := by
        apply e.injective
        apply Subtype.ext
        rw [e1, e2]
      have h12 : i⁻¹ * (k : G) * i = q⁻¹ * (k : G) * q := congrArg Subtype.val hk12
      calc (k : G) * (i * q⁻¹) = i * (i⁻¹ * (k : G) * i) * q⁻¹ := by group
        _ = i * (q⁻¹ * (k : G) * q) * q⁻¹ := by rw [h12]
        _ = (i * q⁻¹) * (k : G) := by group
    have hxC : i * q⁻¹ ∈ centralizerElem u :=
      (centralizerElem u).mul_mem hiu ((centralizerElem u).inv_mem hqC)
    have hxcent : i * q⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact hxK ⟨k, hk⟩
    have hxR : i * q⁻¹ ∈ baum S := by
      have : i * q⁻¹ ∈ centralizerElem u ⊓ Subgroup.centralizer (K : Set G) := ⟨hxC, hxcent⟩
      rw [s.B_eq] at this
      exact this.1
    have hRT : baum S ≤ T := hRS.trans hST
    have hk0T : (k0 : G) ∈ T := by
      have hk0 : (k0 : G) = (i * q⁻¹)⁻¹ * i * r⁻¹ := by rw [hqdef]; group
      rw [hk0]
      exact T.mul_mem (T.mul_mem (T.inv_mem (hRT hxR)) hiT') (T.inv_mem (hRT hr))
    have hk0Tu : (k0 : G) ∈ T ⊓ centralizerElem u := ⟨hk0T, hKC k0.2⟩
    have hTu2 : IsPGroup 2 (T ⊓ centralizerElem u : Subgroup G) := s.Tu_sylow.isPGroup
    have hsyl : K ⊓ (T ⊓ centralizerElem u) = baum S ⊓ K :=
      s.RK_sylow.eq_of_le (X := K ⊓ (T ⊓ centralizerElem u))
        (fun x hx => ⟨hx.2, hRT hx.1, hRC hx.1⟩) inf_le_left hTu2.to_inf_right
    have hk0R : (k0 : G) ∈ baum S := by
      have : (k0 : G) ∈ K ⊓ (T ⊓ centralizerElem u) := ⟨k0.2, hk0Tu⟩
      rw [hsyl] at this
      exact this.1
    have hiR : i ∈ baum S := by
      have h1 := (baum S).mul_mem hxR ((baum S).mul_mem hk0R hr)
      have h2 : i * q⁻¹ * ((k0 : G) * r) = i := by rw [← hqdef]; group
      rwa [h2] at h1
    exact hiS (hRS hiR)
  have hnc : ¬ ∃ σ : Equiv.Perm (Fin 6), ∀ a : Aut6.A6,
      (((e.symm.trans (c.trans e)) a : Aut6.A6) : Equiv.Perm (Fin 6)) =
        σ⁻¹ * (a : Equiv.Perm (Fin 6)) * σ := by
    rintro ⟨σ, hσ⟩
    apply hnoσ
    refine ⟨σ, ?_⟩
    intro k k' hk
    have hk' : k' = c k := Subtype.ext hk
    rw [hk']
    have := hσ (e k)
    simpa using this
  obtain ⟨a₀, ha₀, hfix⟩ := Aut6.a6_fixed_five (e.symm.trans (c.trans e)) hι hnc
  set k₀ : K := e.symm a₀ with hk₀
  have hk₀ord : orderOf (k₀ : G) = 5 := by
    rw [Subgroup.orderOf_coe, hk₀, ← ha₀]
    exact orderOf_injective e.symm.toMonoidHom e.symm.injective a₀
  have hck : c k₀ = k₀ := by
    apply e.injective
    have : e (c k₀) = a₀ := by simpa [hk₀] using hfix
    rw [this, hk₀, MulEquiv.apply_symm_apply]
  have hik : i⁻¹ * (k₀ : G) * i = k₀ := congrArg Subtype.val hck
  have hcomm : (k₀ : G) * i = i * (k₀ : G) := by
    calc (k₀ : G) * i = i * (i⁻¹ * (k₀ : G) * i) := by group
      _ = i * k₀ := by rw [hik]
  have hx₀ : z * (h * (k₀ : G) * h⁻¹) = (h * (k₀ : G) * h⁻¹) * z := by
    have hz : z = h * i * h⁻¹ := by rw [hih]; group
    calc z * (h * (k₀ : G) * h⁻¹) = h * (i * (k₀ : G)) * h⁻¹ := by rw [hz]; group
      _ = h * ((k₀ : G) * i) * h⁻¹ := by rw [hcomm]
      _ = (h * (k₀ : G) * h⁻¹) * z := by rw [hz]; group
  have hx₀M : h * (k₀ : G) * h⁻¹ ∈ M := s.mem_M_of_commute hx₀
  have hx₀ord : orderOf (h * (k₀ : G) * h⁻¹) = 5 := by
    have := orderOf_injective (MulAut.conj h).toMonoidHom (MulAut.conj h).injective (k₀ : G)
    simpa [MulAut.conj_apply, hk₀ord] using this
  have hdvd : orderOf (⟨h * (k₀ : G) * h⁻¹, hx₀M⟩ : M) ∣ Nat.card M := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, hx₀ord, s.M_card] at hdvd
  norm_num at hdvd

theorem lemma2_4_29_11 : Lemma2_4_29_11 := by
  intro G _ _ T M H S L cfg z u K s
  have cs := cfg.cs
  have : IsSimpleGroup G := cs.setting.simple
  have hperf : commutator G = ⊤ := commutator_eq_top_of_simple cs.setting.nonabelian
  obtain ⟨hz1, hz2', hz2⟩ :=
    zpowers_card_two_facts (z := z) (by rw [← s.z_gen]; exact s.Z_card)
  have hu2 : u ^ 2 = 1 := cs.block.1.1.2.2.1.2 u s.u_U
  have hzZ : z ∈ centerOf (borelP M L) := by rw [s.z_gen]; exact Subgroup.mem_zpowers z
  have hzS : z ∈ S := s.P_le hzZ.1
  have hTidx : Nat.Coprime 2 T.index := by
    have h := cs.setting.sylow.2.2
    rw [index_subgroupOf_top] at h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 h
  obtain ⟨j, hjT, hjS, hj2⟩ := s.j_exists
  have hconj_j : ∀ g : G, g⁻¹ * j * g ∉ S := by
    intro g hg
    have hsq : (g⁻¹ * j * g) ^ 2 = g⁻¹ * z * g := by
      rw [← hj2]
      have := conj_pow (a := g⁻¹) (b := j) (i := 2)
      simpa using this
    have hfr : (g⁻¹ * j * g) ^ 2 ∈ frattiniOf S := sq_mem_frattiniOf cs.sylow.isPGroup hg
    rw [hsq] at hfr
    have hP : g⁻¹ * z * g ∈ borelP M L := s.frattini_le hfr
    have hzg : g⁻¹ * z * g = z := s.conj_mem_P hu2 hz1 hz2 hP
    have hgM : g ∈ M := s.mem_M_of_commute (by
      calc z * g = g * (g⁻¹ * z * g) := by group
        _ = g * z := by rw [hzg])
    have hjIS : j ∈ pResidualOf 2 M ⊔ S := by
      have h1 : g⁻¹ * j * g ∈ pResidualOf 2 M ⊔ S := Subgroup.mem_sup_right hg
      exact (Subgroup.mem_set_normalizer_iff''.1 (s.IS_norm hgM) j).2 h1
    have : j ∈ T ⊓ (pResidualOf 2 M ⊔ S) := ⟨hjT, hjIS⟩
    rw [s.IS_inf] at this
    exact hjS this
  obtain ⟨g, hgT, hgS⟩ :=
    exists_conj_sq_mem_sdiff hperf hTidx cs.le_T s.index_two hjT hjS hj2 hz2' hzS hconj_j
  have hiM : g⁻¹ * z * g ∈ M := cs.setting.le hgT
  have hiIS : g⁻¹ * z * g ∉ pResidualOf 2 M ⊔ S := by
    intro h
    have : g⁻¹ * z * g ∈ T ⊓ (pResidualOf 2 M ⊔ S) := ⟨hgT, h⟩
    rw [s.IS_inf] at this
    exact hgS this
  have hi2 : (g⁻¹ * z * g) ^ 2 = 1 := by
    have := conj_pow (a := g⁻¹) (b := z) (i := 2)
    simpa [hz2'] using this
  rcases s.dichotomy _ hiM hiIS hi2 with ⟨Y, c, hYc, hY, hc, hzY⟩ | ⟨m, hm, hmi⟩
  · exact s.case1_false hu2 hz1 hz2 s.P_le hgS Y c hYc hY hc hzY
  · have hi'M : m⁻¹ * (g⁻¹ * z * g) * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm) hiM) hm
    have hi'T : m⁻¹ * (g⁻¹ * z * g) * m ∈ T ⊓ centralizerElem u := by
      rw [s.Tu_eq]; exact ⟨hi'M, hmi⟩
    have hi'S : m⁻¹ * (g⁻¹ * z * g) * m ∉ S := by
      intro h
      apply hiIS
      have h1 : m⁻¹ * (g⁻¹ * z * g) * m ∈ pResidualOf 2 M ⊔ S := Subgroup.mem_sup_right h
      exact (Subgroup.mem_set_normalizer_iff''.1 (s.IS_norm hm) (g⁻¹ * z * g)).2 h1
    have hi'2 : (m⁻¹ * (g⁻¹ * z * g) * m) ^ 2 = 1 := by
      have := conj_pow (a := m⁻¹) (b := g⁻¹ * z * g) (i := 2)
      simpa [hi2] using this
    exact s.case2_false cs.le_T hi'T hi'2 hi'S (h := g * m) (by group)

end Main

end CFSG.QuasithinUnique.A5
