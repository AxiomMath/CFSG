module

public import CFSG.GroupTheory.ThompsonIndexTwo
public import CFSG.GroupTheory.ABGLocalTools.Basic

public section

namespace CFSG.EvenSporTransfer

open Subgroup CFSG.GH74.GLS.Bg.Thompson CFSG.ThompsonIndexTwo CFSG.ABGLocalTools

variable {G : Type*} [Group G] [Finite G]


theorem exists_extremal_conj_of_thompson {T U : Subgroup G} (hT : IsPGroup 2 T)
    (hTidx : ¬ 2 ∣ T.index) (hUT : U ≤ T) (hUidx : U.relIndex T = 2) {x : G} (hxT : x ∈ T)
    (hxU : x ∉ U) (hmin : ∀ y ∈ T, y ∉ U → orderOf x ≤ orderOf y)
    (hno : ∀ N : Subgroup G, N.Normal → N.index ≠ 2) :
    ∃ g : G, g⁻¹ * x * g ∈ U ∧ IsExtremalIn 2 T (g⁻¹ * x * g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : (U.subgroupOf T).Normal := Subgroup.normal_of_index_eq_two hUidx
  have hQn : ∀ t ∈ T, ∀ q ∈ U, t * q * t⁻¹ ∈ U := fun t ht q hq =>
    Subgroup.mem_subgroupOf.1
      (hn.conj_mem ⟨q, hUT hq⟩ (Subgroup.mem_subgroupOf.2 hq) ⟨t, ht⟩)
  have hcyc : ∃ b ∈ T, ∀ t ∈ T, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ U := by
    refine ⟨x, hxT, fun t ht => ?_⟩
    by_cases htU : t ∈ U
    · exact ⟨0, by simpa using htU⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_not_mem hUidx hxT ht hxU htU⟩
  have hord2 : 2 ∣ orderOf x := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hT (⟨x, hxT⟩ : T)
    have hk' : orderOf x = 2 ^ k := (Subgroup.orderOf_coe (⟨x, hxT⟩ : T)).trans hk
    have hk0 : k ≠ 0 := by
      rintro rfl
      have hx1 : x = 1 := orderOf_eq_one_iff.1 (hk'.trans (pow_zero 2))
      exact hxU (by rw [hx1]; exact U.one_mem)
    rw [hk']
    exact dvd_pow_self 2 hk0
  have hb : ∀ (g : G) (k : ℕ), g⁻¹ * x ^ (2 * k) * g ∈ T → g⁻¹ * x ^ (2 * k) * g ∈ U := by
    intro g k hgT
    by_contra hgU
    have hle := hmin _ hgT hgU
    have hpow : (x ^ (2 * k)) ^ orderOf (x ^ 2) = 1 := by
      rw [pow_mul x 2 k, pow_right_comm (x ^ 2) k, pow_orderOf_eq_one, one_pow]
    have hdvd : orderOf (g⁻¹ * x ^ (2 * k) * g) ∣ orderOf (x ^ 2) := by
      apply orderOf_dvd_of_pow_eq_one
      have hc := conj_pow (a := g⁻¹) (b := x ^ (2 * k)) (i := orderOf (x ^ 2))
      rw [inv_inv] at hc
      rw [hc, hpow]
      group
    have h2 : orderOf (x ^ 2) = orderOf x / 2 := orderOf_pow_of_dvd (by norm_num) hord2
    have h3 : orderOf (g⁻¹ * x ^ (2 * k) * g) ≤ orderOf (x ^ 2) :=
      Nat.le_of_dvd (orderOf_pos _) hdvd
    have h4 := orderOf_pos x
    omega
  have hc : ∀ g : G, g⁻¹ * x * g ∈ T → IsExtremalIn 2 T (g⁻¹ * x * g) →
      g⁻¹ * x * g ∈ U ∨ x⁻¹ * (g⁻¹ * x * g) ∈ U := by
    intro g hgT _
    by_cases hgU : g⁻¹ * x * g ∈ U
    · exact Or.inl hgU
    · exact Or.inr (inv_mul_mem_of_not_mem hUidx hxT hgT hxU hgU)
  rcases thompson_transfer_1515 (p := 2) hT hTidx hQn hcyc hxT hxU hb hc with
    ⟨N, hN, -, hNp, hxN⟩ | ⟨g, hg, hext, -⟩
  · exfalso
    have := hN
    have : Group.IsNilpotent (G ⧸ N) := hNp.isNilpotent
    have hbt : (⊥ : Subgroup (G ⧸ N)) ≠ ⊤ := by
      intro h
      apply hxN
      have h1 : (QuotientGroup.mk x : G ⧸ N) ∈ (⊥ : Subgroup (G ⧸ N)) := by
        rw [h]
        exact Subgroup.mem_top _
      exact (QuotientGroup.eq_one_iff x).1 (Subgroup.mem_bot.1 h1)
    obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subgroup (G ⧸ N))).resolve_left hbt
    have hMidx : M.index = 2 := (IsPGroup.isCoatom_iff_index_eq_prime hNp).1 hM
    refine hno (M.comap (QuotientGroup.mk' N)) ((Subgroup.normal_of_index_eq_two hMidx).comap _) ?_
    exact (Subgroup.index_comap_of_surjective M (f := QuotientGroup.mk' N)
      QuotientGroup.mk_surjective).trans hMidx
  · exact ⟨g, hg, hext⟩




omit [Finite G] in
theorem exists_isSylowOf_ge {N A : Subgroup G} (hAN : A ≤ N) (hA : IsPGroup 2 A) :
    ∃ W : Subgroup G, IsSylowOf 2 W N ∧ A ≤ W := by
  have hA' : IsPGroup 2 ↥(A.subgroupOf N) :=
    IsPGroup.of_equiv hA (Subgroup.subgroupOfEquivOfLe hAN).symm
  obtain ⟨Q, hQ⟩ := hA'.exists_le_sylow
  refine ⟨(Q : Subgroup ↥N).map N.subtype, ⟨Q, rfl⟩, fun a ha => ?_⟩
  exact ⟨⟨a, hAN ha⟩, hQ (by simpa [Subgroup.mem_subgroupOf] using ha), rfl⟩

theorem exists_sylow_eq_of_fusion {N W : Subgroup G} {x : G} (hW : IsSylowOf 2 W N) (hxW : x ∈ W)
    (hCx : centralizer ({x} : Set G) ≤ N)
    (hfus : ∀ g : G, g⁻¹ * x * g ∈ N → ∃ n ∈ N, g⁻¹ * x * g = n⁻¹ * x * n) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hWp : IsPGroup 2 W := hW.isPGroup
  obtain ⟨S, hWS⟩ := hWp.exists_le_sylow
  refine ⟨S, ?_⟩
  by_contra hne
  have hlt : W < (S : Subgroup G) := lt_of_le_of_ne hWS (Ne.symm hne)
  have hSp : IsPGroup 2 ↥(S : Subgroup G) := S.isPGroup'
  have : Group.IsNilpotent ↥(S : Subgroup G) := hSp.isNilpotent
  have hnc : NormalizerCondition ↥(S : Subgroup G) := Group.normalizerCondition_of_isNilpotent
  have hW' : W.subgroupOf (S : Subgroup G) < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    obtain ⟨y, hyS, hyW⟩ := IsConcreteLE.exists_of_lt hlt
    have : (⟨y, hyS⟩ : ↥(S : Subgroup G)) ∈ W.subgroupOf (S : Subgroup G) := by rw [htop]; trivial
    exact hyW this
  obtain ⟨s, hsn, hsW⟩ := IsConcreteLE.exists_of_lt (hnc _ hW')
  have hs1 : ∀ w ∈ W, (s : G) * w * (s : G)⁻¹ ∈ W := by
    intro w hw
    have := (mem_normalizer_iff.1 hsn ⟨w, hWS hw⟩).1 (by simpa [Subgroup.mem_subgroupOf] using hw)
    simpa [Subgroup.mem_subgroupOf] using this
  have hs2 : ∀ w ∈ W, (s : G)⁻¹ * w * (s : G) ∈ W := by
    intro w hw
    have := (mem_normalizer_iff.1 (inv_mem hsn) ⟨w, hWS hw⟩).1
      (by simpa [Subgroup.mem_subgroupOf] using hw)
    simpa [Subgroup.mem_subgroupOf] using this
  have hxs : (s : G)⁻¹ * x * (s : G) ∈ N := hW.le (hs2 x hxW)
  obtain ⟨n, hnN, hn⟩ := hfus (s : G) hxs
  have hc : (s : G) * n⁻¹ ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (s : G) * n⁻¹ * x = (s : G) * (n⁻¹ * x * n) * n⁻¹ := by group
      _ = (s : G) * ((s : G)⁻¹ * x * (s : G)) * n⁻¹ := by rw [hn]
      _ = x * ((s : G) * n⁻¹) := by group
  have hsN : (s : G) ∈ N := by
    have := N.mul_mem (hCx hc) hnN
    simpa using this
  have hs_mem : (s : G) ∈ (S : Subgroup G) := s.2
  have hle : W ⊔ zpowers (s : G) ≤ (S : Subgroup G) := sup_le hWS (zpowers_le.2 hs_mem)
  have hleN : W ⊔ zpowers (s : G) ≤ N := sup_le hW.le (zpowers_le.2 hsN)
  have hpg : IsPGroup 2 ↥(W ⊔ zpowers (s : G)) := hSp.to_le hle
  have hWle : W ≤ W ⊔ zpowers (s : G) := le_sup_left
  obtain ⟨-, -, hidx⟩ := (isSylowOf_iff (p := 2)).1 hW
  have hmul := Subgroup.relIndex_mul_relIndex W (W ⊔ zpowers (s : G)) N hWle hleN
  have hdvd : W.relIndex (W ⊔ zpowers (s : G)) ∣ W.relIndex N := ⟨_, hmul.symm⟩
  have hpk : ∃ k : ℕ, W.relIndex (W ⊔ zpowers (s : G)) = 2 ^ k := by
    have hp' : IsPGroup 2 ↥(W ⊔ zpowers (s : G)) := hpg
    exact hp'.index (W.subgroupOf (W ⊔ zpowers (s : G)))
  obtain ⟨k, hk⟩ := hpk
  have hk0 : k = 0 := by
    by_contra hk0
    apply hidx
    exact (dvd_pow_self 2 hk0).trans (hk ▸ hdvd)
  have h1 : W.relIndex (W ⊔ zpowers (s : G)) = 1 := by rw [hk, hk0]; rfl
  have hle2 : W ⊔ zpowers (s : G) ≤ W := Subgroup.relIndex_eq_one.1 h1
  apply hsW
  rw [Subgroup.mem_subgroupOf]
  exact hle2 (mem_sup_right (mem_zpowers _))



omit [Finite G] in
theorem isPGroup_closure_pair {x u : G} (hx : x ^ 2 = 1) (hu : u ^ 2 = 1) (hxu : x * u = u * x) :
    IsPGroup 2 ↥(closure ({x, u} : Set G)) := by
  have hcomm : ({x, u} : Set G).Pairwise Commute := by
    intro a ha b hb _
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact Commute.refl _
    · exact hxu
    · exact hxu.symm
    · exact Commute.refl _
  have hmc : IsMulCommutative ↥(closure ({x, u} : Set G)) := Subgroup.isMulCommutative_closure hcomm
  have key : ∀ z ∈ closure ({x, u} : Set G), z ^ 2 = 1 := by
    intro z hz
    induction hz using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact hx
      · exact hu
    | one => simp
    | mul a b ha hb iha ihb =>
      have hab : a * b = b * a :=
        congrArg Subtype.val (hmc.is_comm.comm (⟨a, ha⟩ : ↥(closure ({x, u} : Set G))) ⟨b, hb⟩)
      rw [(Commute.mul_pow hab 2), iha, ihb, one_mul]
    | inv a ha iha => rw [inv_pow, iha, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using key g g.2)⟩

omit [Finite G] in
theorem relIndex_inf_eq_two {N H W : Subgroup G} (hWN : W ≤ N) (hidx : H.relIndex N = 2) {u : G}
    (huW : u ∈ W) (huH : u ∉ H) : (W ⊓ H).relIndex W = 2 := by
  have hidx' : (H.subgroupOf N).index = 2 := hidx
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨u, huW⟩, fun b => ?_⟩
  have hb := (Subgroup.mul_mem_iff_of_index_two (H := H.subgroupOf N) hidx'
    (a := ⟨b.1, hWN b.2⟩) (b := ⟨u, hWN huW⟩))
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.mem_inf] at hb ⊢
  have hbW : (b : G) ∈ W := b.2
  by_cases h : (b : G) ∈ H
  · have : (b : G) * u ∉ H := fun h' => huH (by simpa [h] using hb.1 h')
    right
    exact ⟨⟨hbW, h⟩, fun h' => this h'.2⟩
  · have : (b : G) * u ∈ H := hb.2 (iff_of_false h huH)
    left
    exact ⟨⟨W.mul_mem hbW huW, this⟩, fun h' => h h'.2⟩

theorem exists_not_fused_of_index_two
    (hno : ∀ M : Subgroup G, M.Normal → M.index ≠ 2)
    {N H : Subgroup G} (hHnorm : ∀ n ∈ N, ∀ h ∈ H, n * h * n⁻¹ ∈ H)
    (hidx : H.relIndex N = 2)
    {x u : G} (hxN : x ∈ N) (hx2 : orderOf x = 2) (huN : u ∈ N) (huH : u ∉ H)
    (hu2 : orderOf u = 2) (hux : u * x = x * u)
    (hCx : centralizer ({x} : Set G) ≤ N) :
    ∃ g : G, g⁻¹ * x * g ∈ N ∧ ∀ n ∈ N, g⁻¹ * x * g ≠ n⁻¹ * x * n := by
  by_contra hcon
  push Not at hcon
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx2' : x ^ 2 = 1 := by rw [← hx2]; exact pow_orderOf_eq_one x
  have hu2' : u ^ 2 = 1 := by rw [← hu2]; exact pow_orderOf_eq_one u
  have hA2 := isPGroup_closure_pair hx2' hu2' hux.symm
  have hAN : closure ({x, u} : Set G) ≤ N := by
    rw [Subgroup.closure_le]
    intro a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
    rcases ha with rfl | rfl
    · exact hxN
    · exact huN
  obtain ⟨W, hW, hAW⟩ := exists_isSylowOf_ge hAN hA2
  have hxW : x ∈ W := hAW (subset_closure (by simp))
  have huW : u ∈ W := hAW (subset_closure (by simp))
  obtain ⟨S, hSW⟩ := exists_sylow_eq_of_fusion hW hxW hCx hcon
  have hWp : IsPGroup 2 W := hW.isPGroup
  have hWidx : ¬ 2 ∣ W.index := by rw [← hSW]; exact S.not_dvd_index
  have hUW : W ⊓ H ≤ W := inf_le_left
  have hUidx : (W ⊓ H).relIndex W = 2 := relIndex_inf_eq_two hW.le hidx huW huH
  have huU : u ∉ W ⊓ H := fun h => huH h.2
  have hmin : ∀ y ∈ W, y ∉ W ⊓ H → orderOf u ≤ orderOf y := by
    intro y _ hyU
    have hy1 : y ≠ 1 := fun h => hyU (h ▸ (W ⊓ H).one_mem)
    have h1 : orderOf y ≠ 1 := fun h => hy1 (orderOf_eq_one_iff.1 h)
    have h2 := orderOf_pos y
    rw [hu2]
    omega
  obtain ⟨g, hgU, hgext⟩ := exists_extremal_conj_of_thompson hWp hWidx hUW hUidx huW huU hmin hno
  have hvH : g⁻¹ * u * g ∈ H := hgU.2
  have hvx' : (g⁻¹ * u * g) * (g⁻¹ * x * g) = (g⁻¹ * x * g) * (g⁻¹ * u * g) := by
    calc (g⁻¹ * u * g) * (g⁻¹ * x * g) = g⁻¹ * (u * x) * g := by group
      _ = g⁻¹ * (x * u) * g := by rw [hux]
      _ = (g⁻¹ * x * g) * (g⁻¹ * u * g) := by group
  have hx'2 : orderOf (g⁻¹ * x * g) = 2 := by
    have := MulEquiv.orderOf_eq (MulAut.conj g⁻¹) x
    simpa [MulAut.conj_apply] using this.trans hx2
  have hKN : zpowers (g⁻¹ * x * g) ≤ centralizer ({g⁻¹ * u * g} : Set G) := by
    rw [zpowers_le, mem_centralizer_singleton_iff]
    exact hvx'.symm
  have hKp : IsPGroup 2 ↥(zpowers (g⁻¹ * x * g)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx'2]; simp)
  obtain ⟨hS₀N, hS₀p, hS₀idx⟩ := hgext
  obtain ⟨c, hcC, hc⟩ := exists_conj_into_sylow hKN hKp hS₀N hS₀p hS₀idx
  have hxk : c⁻¹ * (g⁻¹ * x * g) * c ∈ W ⊓ centralizer ({g⁻¹ * u * g} : Set G) :=
    hc _ (mem_zpowers _)
  have hxgc : (g * c)⁻¹ * x * (g * c) = c⁻¹ * (g⁻¹ * x * g) * c := by group
  have hmem : (g * c)⁻¹ * x * (g * c) ∈ N := by rw [hxgc]; exact hW.le hxk.1
  obtain ⟨n, hnN, hn⟩ := hcon (g * c) hmem
  have hcent : (g * c) * n⁻¹ ∈ centralizer ({x} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc (g * c) * n⁻¹ * x = (g * c) * (n⁻¹ * x * n) * n⁻¹ := by group
      _ = (g * c) * ((g * c)⁻¹ * x * (g * c)) * n⁻¹ := by rw [hn]
      _ = x * ((g * c) * n⁻¹) := by group
  have hgcN : g * c ∈ N := by
    have := N.mul_mem (hCx hcent) hnN
    simpa using this
  have hcv : c⁻¹ * (g⁻¹ * u * g) * c = g⁻¹ * u * g := by
    have h := mem_centralizer_singleton_iff.1 hcC
    calc c⁻¹ * (g⁻¹ * u * g) * c = c⁻¹ * ((g⁻¹ * u * g) * c) := by group
      _ = c⁻¹ * (c * (g⁻¹ * u * g)) := by rw [h]
      _ = g⁻¹ * u * g := by group
  have hu_conj : (g * c)⁻¹ * u * (g * c) = g⁻¹ * u * g := by
    calc (g * c)⁻¹ * u * (g * c) = c⁻¹ * (g⁻¹ * u * g) * c := by group
      _ = g⁻¹ * u * g := hcv
  apply huH
  have h1 := hHnorm (g * c) hgcN _ hvH
  have h2 : (g * c) * (g⁻¹ * u * g) * (g * c)⁻¹ = u := by
    rw [← hu_conj]; group
  rwa [h2] at h1

end CFSG.EvenSporTransfer
