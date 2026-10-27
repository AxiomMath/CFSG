module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.NotationAPI
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Klein
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Residual
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Rank
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.QuasithinUnique

open CFSG.Open CFSG.Quasithin

section Normal

variable {G : Type*} [Group G]

theorem mem_sup_of_le_normalizer {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, x, hx, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    have hconj : b₁ * a₂ * b₁⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hB hb₁) a₂).mp ha₂
    exact ⟨a₁ * (b₁ * a₂ * b₁⁻¹), A.mul_mem ha₁ hconj, b₁ * b₂, B.mul_mem hb₁ hb₂, by group⟩
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    have hconj : b⁻¹ * a⁻¹ * b ∈ A := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (A : Set G)).inv_mem (hB hb))
        a⁻¹).mp (A.inv_mem ha)
      simpa using this
    exact ⟨b⁻¹ * a⁻¹ * b, hconj, b⁻¹, B.inv_mem hb, by group⟩

theorem pow_mul_mem_mul_pow {K S : Subgroup G} (hS : S ≤ Subgroup.normalizer (K : Set G)) {k s : G}
    (hk : k ∈ K) (hs : s ∈ S) (n : ℕ) : ∃ k' ∈ K, (k * s) ^ n = k' * s ^ n := by
  induction n with
  | zero => exact ⟨1, K.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨k', hk', h⟩ := ih
    have hsn : s ^ n ∈ S := S.pow_mem hs n
    have hconj : s ^ n * k * (s ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hS hsn) k).mp hk
    refine ⟨k' * (s ^ n * k * (s ^ n)⁻¹), K.mul_mem hk' hconj, ?_⟩
    rw [pow_succ, h]
    group

end Normal

theorem isElemAbelian_mul_comm {G : Type*} [Group G] {p : ℕ} {E : Subgroup G}
    (h : IsElemAbelian p E) {a b : G} (ha : a ∈ E) (hb : b ∈ E) : a * b = b * a :=
  CFSG.Open.IsElemAbelian.comm h ha hb

section K

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {hs : UnconstrainedSetting G T M}
  (N : Notation25 hs)

theorem Notation25.S_le_normalizer_K (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) :
    N.S ≤ Subgroup.normalizer (N.K : Set G) := fun _ hs' => hKH (N.S_le_H hs')

theorem Notation25.K0_eq (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) : N.K0 = N.K := by
  refine le_antisymm ?_ N.K_le_K0
  refine iSup_le fun s => ?_
  rintro _ ⟨y, hy, rfl⟩
  have hsN : (s : G) ∈ Subgroup.normalizer (N.K : Set G) := N.S_le_normalizer_K hKH s.2
  exact (Subgroup.mem_normalizer_iff.mp hsN y).mp hy

theorem Notation25.exists_mul (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) {x : G}
    (hx : x ∈ N.H) : ∃ k ∈ N.K, ∃ s ∈ N.S, x = k * s := by
  rw [N.join] at hx
  exact mem_sup_of_le_normalizer (N.S_le_normalizer_K hKH) hx

theorem Notation25.odd_mem_K (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G)) {x : G}
    (hx : x ∈ N.H) (hodd : Odd (orderOf x)) : x ∈ N.K := by
  obtain ⟨k, hk, s, hs', rfl⟩ := N.exists_mul hKH hx
  have hs2 : IsPGroup 2 ↥N.S := N.tuple.sylow.isPGroup
  obtain ⟨j, hj⟩ := hs2 ⟨s, hs'⟩
  have hsj : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  obtain ⟨k', hk', h⟩ := pow_mul_mem_mul_pow (N.S_le_normalizer_K hKH) hk hs' (2 ^ j)
  rw [hsj, mul_one] at h
  have hcop : Nat.Coprime (2 ^ j) (orderOf (k * s)) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hodd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm, h]
  exact N.K.pow_mem hk' m

theorem Notation25.center_K_trivial (hsimple : IsSimpleGroup ↥N.K) {x : G} (hx : x ∈ N.K)
    (hc : ∀ y ∈ N.K, x * y = y * x) : x = 1 := by
  obtain ⟨-, ⟨⟨-, -, a, b, hab⟩, -⟩⟩ := N.isComp
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  have hnc : a' * b' ≠ b' * a' := fun h =>
    hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])
  have hnc' : ((a' : ↥N.H) : G) * ((b' : ↥N.H) : G) ≠ ((b' : ↥N.H) : G) * ((a' : ↥N.H) : G) :=
    fun h => hnc (Subtype.ext (Subtype.ext h))
  have ha'K : ((a' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp a'.2
  have hb'K : ((b' : ↥N.H) : G) ∈ N.K := Subgroup.mem_subgroupOf.mp b'.2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥N.K) with h | h
  · have hmem : (⟨x, hx⟩ : ↥N.K) ∈ Subgroup.center ↥N.K := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hc g g.2).symm
    rw [h] at hmem
    exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)
  · exfalso
    have hmem : (⟨((a' : ↥N.H) : G), ha'K⟩ : ↥N.K) ∈ Subgroup.center ↥N.K := by
      rw [h]; exact Subgroup.mem_top _
    have := Subgroup.mem_center_iff.mp hmem ⟨((b' : ↥N.H) : G), hb'K⟩
    exact hnc' (congrArg Subtype.val this).symm

theorem Notation25.mem_S_of_centralizes (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (hZ : ∀ x ∈ N.K, (∀ y ∈ N.K, x * y = y * x) → x = 1) {c : G}
    (hc : c ∈ N.H) (hcK : ∀ f ∈ N.K, c * f = f * c) : c ∈ N.S := by
  set C : Subgroup G := N.H ⊓ Subgroup.centralizer (N.K : Set G) with hC
  have hC2 : IsPGroup 2 ↥C := by
    rintro ⟨x, hxH, hxK⟩
    obtain ⟨k, hk, s, hs', rfl⟩ := N.exists_mul hKH hxH
    obtain ⟨j, hj⟩ := (N.tuple.sylow.isPGroup : IsPGroup 2 ↥N.S) ⟨s, hs'⟩
    have hsj : s ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    obtain ⟨k', hk', h⟩ := pow_mul_mem_mul_pow (N.S_le_normalizer_K hKH) hk hs' (2 ^ j)
    rw [hsj, mul_one] at h
    have hcomm : ∀ f ∈ N.K, (k * s) ^ 2 ^ j * f = f * (k * s) ^ 2 ^ j := fun f hf =>
      (Commute.pow_right (Subgroup.mem_centralizer_iff.mp hxK f hf) _).eq.symm
    have h1 : (k * s) ^ 2 ^ j = 1 := by
      apply hZ _ (by rw [h]; exact hk') hcomm
    exact ⟨j, Subtype.ext (by simpa using h1)⟩
  have hnorm : (C.subgroupOf N.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff inf_le_left]
    intro c' x hc' hx
    refine ⟨N.H.mul_mem (N.H.mul_mem hx hc'.1) (N.H.inv_mem hx), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
    have hxN : x ∈ Subgroup.normalizer (N.K : Set G) := hKH hx
    have hf' : x⁻¹ * f * x ∈ N.K := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer (N.K : Set G)).inv_mem hxN)
        f).mp hf
      simpa using this
    have hcc := Subgroup.mem_centralizer_iff.mp hc'.2 _ hf'
    calc f * (x * c' * x⁻¹) = x * ((x⁻¹ * f * x) * c') * x⁻¹ := by group
      _ = x * (c' * (x⁻¹ * f * x)) * x⁻¹ := by rw [hcc]
      _ = x * c' * x⁻¹ * f := by group
  have hCle : C ≤ pCoreOf 2 N.H :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 C N.H inf_le_left hnorm hC2
  have hcC : c ∈ C := ⟨hc, Subgroup.mem_centralizer_iff.mpr fun f hf => (hcK f hf).symm⟩
  have := hCle hcC
  rw [← h254.SC_eq] at this
  exact N.SC_le_S this

@[expose] noncomputable def Notation25.kleinData (h258 : Facts258 N) {E : Subgroup G}
    (hEK : E ≤ N.SK) (hE4 : IsFourSubgroup E) :
    Klein.Data (N.K ⊓ Subgroup.normalizer (E : Set G)) E where
  φ := (h258.four_normalizer E (hEK.trans inf_le_right) hE4).some
  le := fun _ he => ⟨(hEK.trans inf_le_right) he, Subgroup.le_normalizer he⟩
  normal := inf_le_right
  card := hE4.2

theorem Notation25.mem_S_of_centralizes_four (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) {y : G} (hyH : y ∈ N.H) (hyE : ∀ e ∈ E, y * e = e * y) :
    y ∈ N.S := by
  have hyK : y ∈ Subgroup.normalizer (N.K : Set G) := hKH hyH
  have hφ : conjAct N.K ⟨y, hyK⟩ ∈ autOn N.H N.K :=
    Subgroup.mem_map.mpr ⟨⟨y, hyK⟩, Subgroup.mem_subgroupOf.mpr hyH, rfl⟩
  have hφE : ∀ f : ↥N.K, (f : G) ∈ E → ((conjAct N.K ⟨y, hyK⟩ f : ↥N.K) : G) = f := by
    intro f hf
    show y * f * y⁻¹ = f
    rw [hyE f hf]
    group
  obtain ⟨s, hsS, hs⟩ := Subgroup.mem_map.mp (h258.four_centralizer E hEK hE4 _ hφ hφE)
  have hsS' : (s : G) ∈ N.S := Subgroup.mem_subgroupOf.mp hsS
  have hcK : ∀ f ∈ N.K, (s : G)⁻¹ * y * f = f * ((s : G)⁻¹ * y) := by
    intro f hf
    have h1 := congrArg (fun φ : MulAut ↥N.K => ((φ ⟨f, hf⟩ : ↥N.K) : G)) hs
    change (s : G) * f * (s : G)⁻¹ = y * f * y⁻¹ at h1
    calc (s : G)⁻¹ * y * f = (s : G)⁻¹ * (y * f * y⁻¹) * y := by group
      _ = (s : G)⁻¹ * ((s : G) * f * (s : G)⁻¹) * y := by rw [h1]
      _ = f * ((s : G)⁻¹ * y) := by group
  have hmem : (s : G)⁻¹ * y ∈ N.S :=
    N.mem_S_of_centralizes hKH h254 (fun x hx hc => N.center_K_trivial h258.simple hx hc)
      (N.H.mul_mem (N.H.inv_mem (N.S_le_H hsS')) hyH) hcK
  have : y = (s : G) * ((s : G)⁻¹ * y) := by group
  rw [this]
  exact N.S.mul_mem hsS' hmem

theorem Notation25.exists_mul_centralizer_normalizer (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) {x : G} (hxH : x ∈ N.H) (hxE : x ∈ Subgroup.normalizer (E : Set G)) :
    ∃ y ∈ N.S ⊓ Subgroup.centralizer (E : Set G),
      ∃ n ∈ N.K ⊓ Subgroup.normalizer (E : Set G), x = y * n := by
  obtain ⟨a, b, ha, hb, ha1, hb1, hab, hgen, hconj⟩ := (N.kleinData h258 hEK hE4).exists_gens
  have hxinv : x⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer (E : Set G)).inv_mem hxE
  have hconjE : ∀ e ∈ E, x⁻¹ * e * x ∈ E := fun e he => by
    have := (Subgroup.mem_normalizer_iff.mp hxinv e).mp he
    simpa using this
  have hne1 : ∀ e : G, e ≠ 1 → x⁻¹ * e * x ≠ 1 := fun e he h => he (by
    calc e = x * (x⁻¹ * e * x) * x⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hab' : x⁻¹ * a * x ≠ x⁻¹ * b * x := fun h => hab (by
    calc a = x * (x⁻¹ * a * x) * x⁻¹ := by group
      _ = x * (x⁻¹ * b * x) * x⁻¹ := by rw [h]
      _ = b := by group)
  obtain ⟨n, hnP, hna, hnb⟩ := hconj _ (hconjE a ha) _ (hconjE b hb) (hne1 a ha1) (hne1 b hb1) hab'
  have hn : n ∈ N.K ⊓ Subgroup.normalizer (E : Set G) := hnP
  have hya : (x * n⁻¹)⁻¹ * a * (x * n⁻¹) = a := by
    calc (x * n⁻¹)⁻¹ * a * (x * n⁻¹) = n * (x⁻¹ * a * x) * n⁻¹ := by group
      _ = n * (n⁻¹ * a * n) * n⁻¹ := by rw [← hna]
      _ = a := by group
  have hyb : (x * n⁻¹)⁻¹ * b * (x * n⁻¹) = b := by
    calc (x * n⁻¹)⁻¹ * b * (x * n⁻¹) = n * (x⁻¹ * b * x) * n⁻¹ := by group
      _ = n * (n⁻¹ * b * n) * n⁻¹ := by rw [← hnb]
      _ = b := by group
  have hcomma : (x * n⁻¹) * a = a * (x * n⁻¹) := by
    calc (x * n⁻¹) * a = (x * n⁻¹) * ((x * n⁻¹)⁻¹ * a * (x * n⁻¹)) := by rw [hya]
      _ = a * (x * n⁻¹) := by group
  have hcommb : (x * n⁻¹) * b = b * (x * n⁻¹) := by
    calc (x * n⁻¹) * b = (x * n⁻¹) * ((x * n⁻¹)⁻¹ * b * (x * n⁻¹)) := by rw [hyb]
      _ = b * (x * n⁻¹) := by group
  have hyE : ∀ e ∈ E, (x * n⁻¹) * e = e * (x * n⁻¹) := by
    intro e he
    rcases hgen e he with rfl | rfl | rfl | rfl
    · simp
    · exact hcomma
    · exact hcommb
    · calc (x * n⁻¹) * (a * b) = ((x * n⁻¹) * a) * b := by group
        _ = a * ((x * n⁻¹) * b) := by rw [hcomma]; group
        _ = a * (b * (x * n⁻¹)) := by rw [hcommb]
        _ = (a * b) * (x * n⁻¹) := by group
  have hyH : x * n⁻¹ ∈ N.H := N.H.mul_mem hxH (N.H.inv_mem (N.K_le_H hn.1))
  have hyS : x * n⁻¹ ∈ N.S :=
    N.mem_S_of_centralizes_four hKH h254 h258 hEK hE4 hyH hyE
  refine ⟨x * n⁻¹, ⟨hyS, Subgroup.mem_centralizer_iff.mpr fun e he => (hyE e he).symm⟩, n, hn, ?_⟩
  group

theorem Notation25.exists_mul_normalizer_centralizer (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) {x : G} (hxH : x ∈ N.H) (hxE : x ∈ Subgroup.normalizer (E : Set G)) :
    ∃ n ∈ N.K ⊓ Subgroup.normalizer (E : Set G),
      ∃ y ∈ N.S ⊓ Subgroup.centralizer (E : Set G), x = n * y := by
  obtain ⟨y, hy, n, hn, h⟩ := N.exists_mul_centralizer_normalizer hKH h254 h258 hEK hE4 (N.H.inv_mem hxH)
    ((Subgroup.normalizer (E : Set G)).inv_mem hxE)
  refine ⟨n⁻¹, ⟨N.K.inv_mem hn.1, (Subgroup.normalizer (E : Set G)).inv_mem hn.2⟩, y⁻¹,
    ⟨N.S.inv_mem hy.1, (Subgroup.centralizer (E : Set G)).inv_mem hy.2⟩, ?_⟩
  rw [← inv_inv x, h, mul_inv_rev]

theorem Notation25.charTwo_normalizer (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) : CharTwo (N.H ⊓ Subgroup.normalizer (E : Set G)) := by
  set X : Subgroup G := N.H ⊓ Subgroup.normalizer (E : Set G) with hX
  set C : Subgroup G := N.H ⊓ Subgroup.centralizer (E : Set G) with hC
  have hES : E ≤ N.S := hEK.trans inf_le_left
  have hCS : C ≤ N.S := fun c hc =>
    N.mem_S_of_centralizes_four hKH h254 h258 hEK hE4 hc.1
      (fun e he => (Subgroup.mem_centralizer_iff.mp hc.2 e he).symm)
  have hC2 : IsPGroup 2 ↥C := N.tuple.sylow.isPGroup.to_le hCS
  have hCX : C ≤ X := fun c hc => ⟨hc.1, Subgroup.centralizer_le_normalizer _ hc.2⟩
  have hnorm : (C.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCX]
    intro c x hc hx
    refine ⟨N.H.mul_mem (N.H.mul_mem hx.1 hc.1) (N.H.inv_mem hx.1), ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (E : Set G) := (Subgroup.normalizer (E : Set G)).inv_mem hx.2
    have he' : x⁻¹ * e * x ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp hxinv e).mp he
      simpa using this
    have hcc := Subgroup.mem_centralizer_iff.mp hc.2 _ he'
    calc e * (x * c * x⁻¹) = x * ((x⁻¹ * e * x) * c) * x⁻¹ := by group
      _ = x * (c * (x⁻¹ * e * x)) * x⁻¹ := by rw [hcc]
      _ = x * c * x⁻¹ * e := by group
  have hCO : C ≤ pCoreOf 2 X :=
    CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 C X hCX hnorm hC2
  have hEC : E ≤ C := fun e he =>
    ⟨N.S_le_H (hES he), Subgroup.mem_centralizer_iff.mpr fun e' he' =>
      isElemAbelian_mul_comm hE4.1 he' he⟩
  intro x hx
  have hxE : x ∈ Subgroup.centralizer (E : Set G) :=
    Subgroup.centralizer_le (by exact_mod_cast (hEC.trans hCO)) hx.2
  exact hCO ⟨hx.1.1, hxE⟩

theorem Notation25.SK_le_S : N.SK ≤ N.S := inf_le_left

theorem Notation25.SK_le_K : N.SK ≤ N.K := inf_le_right

theorem Notation25.exists_sigma (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) : ∃ σ ∈ N.SK ⊓ Subgroup.normalizer (E : Set G), σ ∉ E := by
  have hSK2 : IsPGroup 2 ↥N.SK := N.tuple.sylow.isPGroup.to_le N.SK_le_S
  have hne : E ≠ N.SK := by
    intro h
    have h8 := eight_le_card_of_shape h258.SK_shape
    rw [← h, hE4.2] at h8
    omega
  obtain ⟨y, hy, hyE⟩ := exists_mem_inf_normalizer_of_ne (p := 2) hSK2 hEK hne
  exact ⟨y, hy, hyE⟩

theorem Notation25.exists_mul_A (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) {x : G} (hxH : x ∈ N.H) (hxE : x ∈ Subgroup.normalizer (E : Set G)) :
    ∃ a ∈ (N.kleinData h258 hEK hE4).A, ∃ y ∈ N.S ⊓ Subgroup.normalizer (E : Set G),
      x = a * y := by
  obtain ⟨n, hn, y₀, hy₀, hxn⟩ := N.exists_mul_normalizer_centralizer hKH h254 h258 hEK hE4 hxH hxE
  have hy₀N : y₀ ∈ N.S ⊓ Subgroup.normalizer (E : Set G) :=
    ⟨hy₀.1, Subgroup.centralizer_le_normalizer _ hy₀.2⟩
  by_cases hnA : n ∈ (N.kleinData h258 hEK hE4).A
  · exact ⟨n, hnA, y₀, hy₀N, hxn⟩
  · obtain ⟨σ, hσ, hσE⟩ := N.exists_sigma h258 hEK hE4
    have hσP : σ ∈ N.K ⊓ Subgroup.normalizer (E : Set G) := ⟨N.SK_le_K hσ.1, hσ.2⟩
    have hσA : σ ∉ (N.kleinData h258 hEK hE4).A := by
      intro hσA
      obtain ⟨j, hj⟩ := (N.tuple.sylow.isPGroup : IsPGroup 2 ↥N.S) ⟨σ, N.SK_le_S hσ.1⟩
      exact hσE ((N.kleinData h258 hEK hE4).two_mem_E hσA (k := j)
        (by simpa using congrArg Subtype.val hj))
    have hnσ : n * σ⁻¹ ∈ (N.kleinData h258 hEK hE4).A :=
      (N.kleinData h258 hEK hE4).mul_inv_mem_A hn hσP hnA hσA
    refine ⟨n * σ⁻¹, hnσ, σ * y₀, ⟨N.S.mul_mem (N.SK_le_S hσ.1) hy₀.1, ?_⟩, ?_⟩
    · exact (Subgroup.normalizer (E : Set G)).mul_mem hσ.2 hy₀N.2
    · rw [hxn]
      group

theorem Notation25.isSylowTwoOf_normalizer (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h254 : Facts254 N) (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) :
    IsSylowTwoOf (N.S ⊓ Subgroup.normalizer (E : Set G)) (N.H ⊓ Subgroup.normalizer (E : Set G)) := by
  have hYX : N.S ⊓ Subgroup.normalizer (E : Set G) ≤ N.H ⊓ Subgroup.normalizer (E : Set G) :=
    inf_le_inf_right _ N.S_le_H
  have hY2 : IsPGroup 2 ↥(N.S ⊓ Subgroup.normalizer (E : Set G)) :=
    N.tuple.sylow.isPGroup.to_le inf_le_left
  obtain ⟨Y', hYY', hY'⟩ := exists_isSylowTwoOf_of_le hYX hY2
  have hQY : N.SK ⊓ Subgroup.normalizer (E : Set G) ≤ N.S ⊓ Subgroup.normalizer (E : Set G) :=
    inf_le_inf_right _ N.SK_le_S
  have hQP : N.SK ⊓ Subgroup.normalizer (E : Set G) ≤ N.K ⊓ Subgroup.normalizer (E : Set G) :=
    inf_le_inf_right _ N.SK_le_K
  have hQ2 : IsPGroup 2 ↥(N.SK ⊓ Subgroup.normalizer (E : Set G)) :=
    N.tuple.sylow.isPGroup.to_le (hQY.trans inf_le_left)
  have hQcard : 8 ≤ Nat.card ↥(N.SK ⊓ Subgroup.normalizer (E : Set G)) := by
    obtain ⟨σ, hσ, hσE⟩ := N.exists_sigma h258 hEK hE4
    have hEQ : E ≤ N.SK ⊓ Subgroup.normalizer (E : Set G) := le_inf hEK Subgroup.le_normalizer
    have hlt : E < N.SK ⊓ Subgroup.normalizer (E : Set G) :=
      lt_of_le_of_ne hEQ (fun h => hσE (h ▸ hσ))
    have h4 : 4 < Nat.card ↥(N.SK ⊓ Subgroup.normalizer (E : Set G)) := by
      have := Subgroup.card_lt_of_lt hlt
      rwa [hE4.2] at this
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hQ2.exists_card_eq
    rw [hj] at h4 ⊢
    have hj3 : 3 ≤ j := by
      by_contra hcon
      have : 2 ^ j ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj3
  have hY'Y : Y' ≤ N.S ⊓ Subgroup.normalizer (E : Set G) := by
    intro y' hy'
    obtain ⟨n, hn, c, hc, hxn⟩ := N.exists_mul_normalizer_centralizer hKH h254 h258 hEK hE4 (hY'.le hy').1
      (hY'.le hy').2
    have hcY : c ∈ N.S ⊓ Subgroup.normalizer (E : Set G) :=
      ⟨hc.1, Subgroup.centralizer_le_normalizer _ hc.2⟩
    have hcY' : c ∈ Y' := hYY' hcY
    have hnY' : n ∈ Y' := by
      have : n = y' * c⁻¹ := by rw [hxn]; group
      rw [this]
      exact Y'.mul_mem hy' (Y'.inv_mem hcY')
    have hQP' : N.SK ⊓ Subgroup.normalizer (E : Set G) ≤
        Y' ⊓ (N.K ⊓ Subgroup.normalizer (E : Set G)) := le_inf (hQY.trans hYY') hQP
    have hP'2 : IsPGroup 2 ↥(Y' ⊓ (N.K ⊓ Subgroup.normalizer (E : Set G))) :=
      hY'.isPGroup.to_le inf_le_left
    have hP'card : Nat.card ↥(Y' ⊓ (N.K ⊓ Subgroup.normalizer (E : Set G))) ≤ 8 :=
      (N.kleinData h258 hEK hE4).card_le_of_isPGroup inf_le_right hP'2
    have hQeq : N.SK ⊓ Subgroup.normalizer (E : Set G) =
        Y' ⊓ (N.K ⊓ Subgroup.normalizer (E : Set G)) :=
      Subgroup.eq_of_le_of_card_ge hQP' (hP'card.trans hQcard)
    have hnQ : n ∈ N.SK ⊓ Subgroup.normalizer (E : Set G) := by
      rw [hQeq]
      exact ⟨hnY', hn⟩
    rw [hxn]
    exact (N.S ⊓ Subgroup.normalizer (E : Set G)).mul_mem (hQY hnQ) hcY
  have hYeq : N.S ⊓ Subgroup.normalizer (E : Set G) = Y' := le_antisymm hYY' hY'Y
  rw [hYeq]
  exact hY'

theorem Notation25.pResidualOf_eq_A (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK) (hE4 : IsFourSubgroup E)
    {X : Subgroup G} (hXH : X ≤ N.H) (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hEX : E ≤ X)
    (hodd : ∃ d ∈ X, d ≠ 1 ∧ Odd (orderOf d)) :
    pResidualOf 2 X = (N.kleinData h258 hEK hE4).A := by
  rw [pResidualOf_two_eq_closure_odd]
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x ⟨hxX, hxodd⟩
    have hxK : x ∈ N.K := N.odd_mem_K hKH (hXH hxX) hxodd
    exact (N.kleinData h258 hEK hE4).odd_mem_A ⟨hxK, hXE hxX⟩ hxodd
  · obtain ⟨d, hdX, hd1, hdodd⟩ := hodd
    have hdK : d ∈ N.K := N.odd_mem_K hKH (hXH hdX) hdodd
    have hdA : d ∈ (N.kleinData h258 hEK hE4).A :=
      (N.kleinData h258 hEK hE4).odd_mem_A ⟨hdK, hXE hdX⟩ hdodd
    refine (N.kleinData h258 hEK hE4).A_le_of_conj hdA hdodd hd1
      (X := Subgroup.closure {x : G | x ∈ X ∧ Odd (orderOf x)}) ?_
    intro e he
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · exact X.mul_mem (X.mul_mem (X.inv_mem (hEX he)) hdX) (hEX he)
    · have : orderOf (e⁻¹ * d * e) = orderOf d := by
        have := (MulAut.conj e⁻¹).orderOf_eq d
        simpa [MulAut.conj_apply] using this
      rw [this]
      exact hdodd

theorem Notation25.pCoreOf_pResidualOf_eq (hKH : N.H ≤ Subgroup.normalizer (N.K : Set G))
    (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK) (hE4 : IsFourSubgroup E)
    {X : Subgroup G} (hXH : X ≤ N.H) (hXE : X ≤ Subgroup.normalizer (E : Set G)) (hEX : E ≤ X)
    (hodd : ∃ d ∈ X, d ≠ 1 ∧ Odd (orderOf d)) : pCoreOf 2 (pResidualOf 2 X) = E := by
  rw [N.pResidualOf_eq_A hKH h258 hEK hE4 hXH hXE hEX hodd]
  have hE2 : IsPGroup 2 ↥E := N.tuple.sylow.isPGroup.to_le (hEK.trans N.SK_le_S)
  apply le_antisymm
  · intro x hx
    have hxA : x ∈ (N.kleinData h258 hEK hE4).A :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_le 2 _ hx
    have h2 : IsPGroup 2 ↥(pCoreOf 2 (N.kleinData h258 hEK hE4).A) :=
      CFSG.RankThreeCoreUniqueness.Helpers.pCoreOf_isPGroup 2 _
    obtain ⟨k, hk⟩ := h2 ⟨x, hx⟩
    exact (N.kleinData h258 hEK hE4).two_mem_E hxA (k := k) (by simpa using congrArg Subtype.val hk)
  · have hnorm : (E.subgroupOf (N.kleinData h258 hEK hE4).A).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (N.kleinData h258 hEK hE4).E_le_A).mpr
        ((N.kleinData h258 hEK hE4).A_le.trans (N.kleinData h258 hEK hE4).normal)
    exact CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCoreOf 2 E _
      (N.kleinData h258 hEK hE4).E_le_A hnorm hE2

theorem Notation25.inf_centralizer_eq (h258 : Facts258 N) {E : Subgroup G} (hEK : E ≤ N.SK)
    (hE4 : IsFourSubgroup E) : N.K ⊓ Subgroup.centralizer (E : Set G) = E := by
  apply le_antisymm
  · intro x hx
    exact (N.kleinData h258 hEK hE4).centralizer ⟨hx.1, Subgroup.centralizer_le_normalizer _ hx.2⟩
      (fun e he => (Subgroup.mem_centralizer_iff.mp hx.2 e he).symm)
  · intro e he
    exact ⟨N.SK_le_K (hEK he), Subgroup.mem_centralizer_iff.mpr fun e' he' =>
      isElemAbelian_mul_comm hE4.1 he' he⟩

end K

end CFSG.QuasithinUnique
