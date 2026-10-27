module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec12b.Lemma12_9f

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec12b

open Subgroup CFSG.GH74.GLS.Stage1.Thm6 CFSG.GH74.GLS.Stage1.Thm6.Sec12

structure NData {G : Type} [Group G] (S T Rd N : Subgroup G) (g₀ w : G) : Prop where
  Rd_le : Rd ≤ N
  le_S : N ≤ S
  normal : ∀ t ∈ S, ∀ q ∈ N, t * q * t⁻¹ ∈ N
  inter : ∀ y ∈ N, y ∈ T → y ∈ Rd
  w_not : w ∉ N
  g₀_mem : g₀ ∈ S
  cyc : ∀ t ∈ S, ∃ k : ℤ, (g₀ ^ k)⁻¹ * t ∈ N

section

variable {G : Type} [Group G] [Finite G] {x z : G} {S T P Q Rd F : Subgroup G} {a : G}
  {V P₁ F' : Subgroup G}

namespace Ph1

theorem NData_of_b₀ (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') (hF : F' ≠ Subgroup.zpowers x) {f : G} (hfF : f ∈ F')
    (hTgen : ∀ t ∈ T, ∃ k : ℤ, ∃ r ∈ Rd, t = f ^ k * r) {b₀ : G} (hb₀S : b₀ ∈ S)
    (hb₀T : b₀ ∉ T) (hb₀2 : b₀ * b₀ ∈ Rd) {w : G} (hwRd : w ∉ Rd) (hwT : w ∈ T) :
    NData S T Rd (Rd ⊔ Subgroup.zpowers b₀) f w := by
  have hcomm := B.S_comm_Rd H A hF
  have hRdS : Rd ≤ S := H.base.Rd_le_T.trans H.base.T_le_S
  have hNorm : NormalIn Rd S := ⟨hRdS, B.Rd_normalS H A⟩
  have hb₀N : b₀ ∈ Rd ⊔ Subgroup.zpowers b₀ := Subgroup.mem_sup_right (Subgroup.mem_zpowers b₀)
  have hmem : ∀ y ∈ Rd ⊔ Subgroup.zpowers b₀, y ∈ Rd ∨ ∃ r ∈ Rd, y = b₀ * r := by
    intro y hy
    obtain ⟨a', ha', r, hr, hyd⟩ := mem_sup_zpowers_of_normalIn hNorm hb₀S hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha'
    obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' j
    · left
      have e : b₀ ^ (2 * m) = (b₀ * b₀) ^ m := by rw [zpow_mul, zpow_two]
      rw [hyd, e]
      exact Rd.mul_mem (Rd.zpow_mem hb₀2 m) hr
    · right
      have e : b₀ ^ (2 * m + 1) = b₀ * (b₀ * b₀) ^ m := by
        rw [zpow_add_one, zpow_mul, zpow_two]
        exact ((Commute.refl b₀).mul_right (Commute.refl b₀)).zpow_right m |>.symm.eq
      refine ⟨(b₀ * b₀) ^ m * r, Rd.mul_mem (Rd.zpow_mem hb₀2 m) hr, ?_⟩
      rw [hyd, e, mul_assoc]
  have hinter : ∀ y ∈ Rd ⊔ Subgroup.zpowers b₀, y ∈ T → y ∈ Rd := by
    intro y hy hyT
    rcases hmem y hy with h | ⟨r, hr, hyr⟩
    · exact h
    · exfalso
      apply hb₀T
      have : b₀ = y * r⁻¹ := by rw [hyr]; group
      rw [this]
      exact T.mul_mem hyT (T.inv_mem (H.base.Rd_le_T hr))
  have hnormal : ∀ t ∈ S, ∀ q ∈ Rd ⊔ Subgroup.zpowers b₀, t * q * t⁻¹ ∈ Rd ⊔ Subgroup.zpowers b₀ := by
    intro t ht
    have hle : Rd ⊔ Subgroup.zpowers b₀ ≤ Hconj t (Rd ⊔ Subgroup.zpowers b₀) := by
      refine sup_le (fun r hr => ?_) ((Subgroup.zpowers_le).2 ?_)
      · rw [mem_Hconj]; exact Subgroup.mem_sup_left (B.Rd_normalS H A t ht r hr)
      · rw [mem_Hconj]
        have e : t * b₀ * t⁻¹ = (t * b₀ * t⁻¹ * b₀⁻¹) * b₀ := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hcomm t ht b₀ hb₀S)) hb₀N
    intro q hq
    exact mem_Hconj.1 (hle hq)
  refine ⟨le_sup_left, sup_le hRdS ((Subgroup.zpowers_le).2 hb₀S), hnormal, hinter,
    fun hw => hwRd (hinter w hw hwT), H.base.T_le_S (B.F_le hfF), ?_⟩
  intro t ht
  by_cases htT : t ∈ T
  · obtain ⟨k, r, hr, htk⟩ := hTgen t htT
    refine ⟨k, ?_⟩
    have : (f ^ k)⁻¹ * t = r := by rw [htk]; group
    rw [this]; exact Subgroup.mem_sup_left hr
  · have hcos : b₀⁻¹ * t ∈ T := H.coset_eq hb₀S ht hb₀T htT
    obtain ⟨k, r, hr, htk⟩ := hTgen _ hcos
    refine ⟨k, ?_⟩
    have hfS : f ∈ S := H.base.T_le_S (B.F_le hfF)
    have hc := hcomm (f ^ k)⁻¹ (S.inv_mem (S.zpow_mem hfS k)) b₀ hb₀S
    have e : (f ^ k)⁻¹ * t = ((f ^ k)⁻¹ * b₀ * (f ^ k)⁻¹⁻¹ * b₀⁻¹) * b₀ * r := by
      have e1 : t = b₀ * (f ^ k * r) := by rw [← htk]; group
      rw [e1]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) hb₀N)
      (Subgroup.mem_sup_left hr)

theorem NData_of_odd (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {f : G} (hfF : f ∈ F')
    (hTgen : ∀ t ∈ T, ∃ k : ℤ, ∃ r ∈ Rd, t = f ^ k * r) {j : ℤ} {r : G} (hr : r ∈ Rd)
    (haj : a * a = f ^ j * r) (hj : Odd j) {w : G} (hwRd : w ∉ Rd) :
    NData S T Rd Rd a w := by
  have hRdS : Rd ≤ S := H.base.Rd_le_T.trans H.base.T_le_S
  have hfT : f ∈ T := B.F_le hfF
  have hpow : ∀ u ∈ S, ∀ n ∈ Rd, ∀ e : ℤ, ∃ n' ∈ Rd, (u * n) ^ e = u ^ e * n' := by
    intro u hu n hn e
    induction e using Int.induction_on with
    | zero => exact ⟨1, Rd.one_mem, by simp⟩
    | succ i ih =>
      obtain ⟨n', hn', h⟩ := ih
      have h1 : u⁻¹ * n' * u ∈ Rd := by
        have := B.Rd_normalS H A u⁻¹ (S.inv_mem hu) n' hn'
        simpa using this
      refine ⟨u⁻¹ * n' * u * n, Rd.mul_mem h1 hn, ?_⟩
      rw [zpow_add_one, h, zpow_add_one]; group
    | pred i ih =>
      obtain ⟨n', hn', h⟩ := ih
      refine ⟨u * (n' * n⁻¹) * u⁻¹, B.Rd_normalS H A u hu _ (Rd.mul_mem hn' (Rd.inv_mem hn)), ?_⟩
      rw [zpow_sub_one, h]; group
  obtain ⟨e, he⟩ := (IsPGroup.iff_orderOf.1 H.base.T_pgroup) ⟨f, hfT⟩
  have hfo : f ^ (2 ^ e) = 1 := by
    have : orderOf f = 2 ^ e := by rw [← he]; exact (Subgroup.orderOf_mk f hfT).symm
    rw [← this]; exact pow_orderOf_eq_one f
  have hfo' : f ^ ((2 : ℤ) ^ e) = 1 := by
    have := zpow_natCast f (2 ^ e)
    push_cast at this
    rw [this]; exact hfo
  obtain ⟨m, hm⟩ := hj
  have hcop : IsCoprime ((2 : ℤ) ^ e) j := by
    have h2 : IsCoprime (2 : ℤ) j := ⟨-m, 1, by rw [hm]; ring⟩
    exact IsCoprime.pow_left h2
  obtain ⟨u', j', hu'⟩ := hcop
  have hf_eq : f = (f ^ j) ^ j' := by
    have h1 : f ^ (u' * 2 ^ e + j' * j) = f ^ (u' * 2 ^ e) * f ^ (j' * j) := zpow_add _ _ _
    have h2 : f ^ (u' * 2 ^ e) = 1 := by rw [mul_comm, zpow_mul, hfo', one_zpow]
    rw [hu', zpow_one, h2, one_mul, mul_comm, zpow_mul] at h1
    exact h1
  have hfj : f ^ j = (a * a) * r⁻¹ := (mul_inv_eq_iff_eq_mul.2 haj).symm
  obtain ⟨n₁, hn₁, hf₁⟩ := hpow (a * a) (S.mul_mem A.a_mem A.a_mem) r⁻¹ (Rd.inv_mem hr) j'
  have hf2 : f = a ^ (2 * j') * n₁ := by
    rw [hf_eq, hfj, hf₁, ← zpow_two, ← zpow_mul]
  have hcycT : ∀ t ∈ T, ∃ m : ℤ, (a ^ m)⁻¹ * t ∈ Rd := by
    intro t ht
    obtain ⟨k, r₂, hr₂, htk⟩ := hTgen t ht
    obtain ⟨n₂, hn₂, hf₂⟩ := hpow (a ^ (2 * j')) (S.zpow_mem A.a_mem _) n₁ hn₁ k
    refine ⟨2 * j' * k, ?_⟩
    have e : (a ^ (2 * j' * k))⁻¹ * t = n₂ * r₂ := by
      rw [htk, hf2, hf₂, ← zpow_mul]; group
    rw [e]; exact Rd.mul_mem hn₂ hr₂
  have hcyc : ∀ t ∈ S, ∃ m : ℤ, (a ^ m)⁻¹ * t ∈ Rd := by
    intro t ht
    by_cases htT : t ∈ T
    · exact hcycT t htT
    · obtain ⟨m, hm'⟩ := hcycT _ (H.coset_eq A.a_mem ht A.a_not htT)
      refine ⟨m + 1, ?_⟩
      have e : (a ^ (m + 1))⁻¹ * t = (a ^ m)⁻¹ * (a⁻¹ * t) := by group
      rw [e]; exact hm'
  exact ⟨le_rfl, hRdS, B.Rd_normalS H A, fun y hy _ => hy, hwRd, A.a_mem, hcyc⟩

theorem inv_coset (H : Hyp129 G x z S T P Q Rd F) (A : Ph0 G x z S T P a)
    (B : Ph1 G x z T P Rd a V P₁ F') {w : G} (hwF : w ∈ F') (hww : w * w = x)
    {N : Subgroup G} {g₀ : G} (Nd : NData S T Rd N g₀ w) :
    ∃ v : G, v ∈ S ∧ v ∉ T ∧ v * v = 1 ∧ w⁻¹ * v ∈ N := by
  by_contra hcon
  have hcon' : ∀ v : G, v ∈ S → v ∉ T → v * v = 1 → w⁻¹ * v ∉ N :=
    fun v hv hvT hv2 hvN => hcon ⟨v, hv, hvT, hv2, hvN⟩
  have hwT : w ∈ T := B.F_le hwF
  have hwS : w ∈ S := H.base.T_le_S hwT
  have hxN : x ∈ N := Nd.Rd_le H.x_mem_Rd
  have hwwN : w * w ∈ N := by rw [hww]; exact hxN
  have hnoinv : ∀ v ∈ S, v * v = 1 → w⁻¹ * v ∉ N := by
    intro v hvS hv2 hvN
    by_cases hvT : v ∈ T
    · have hvRd : v ∈ Rd := H.h127.omega1_le (Subgroup.subset_closure ⟨hvT, hv2⟩)
      apply Nd.w_not
      have : w = v * (w⁻¹ * v)⁻¹ := by group
      rw [this]
      exact N.mul_mem (Nd.Rd_le hvRd) (N.inv_mem hvN)
    · exact hcon' v hvS hvT hv2 hvN
  have hne : N ≠ S := fun e => Nd.w_not (e ▸ hwS)
  have hw4 : orderOf w = 4 := by
    have h1 : ¬ w ^ 2 ^ 1 = 1 := by
      intro h
      rw [pow_one, pow_two, hww] at h
      exact H.base.x_ne_one h
    have h2 : w ^ 2 ^ (1 + 1) = 1 := by
      have : w ^ 2 ^ (1 + 1) = w ^ 4 := by norm_num
      rw [this]; exact w_pow4 H hww
    have := orderOf_eq_prime_pow h1 h2
    simpa using this
  have hord : ∀ v ∈ S, v ∉ N → orderOf w ≤ orderOf v := by
    intro v hvS hvN
    rw [hw4]
    have hv1 : v ≠ 1 := fun e => hvN (by rw [e]; exact N.one_mem)
    have hv2 : v * v ≠ 1 := by
      intro hv2
      have h1 := uniq_inv_coset Nd.normal Nd.g₀_mem Nd.cyc hvS hwS hvN Nd.w_not
        (by rw [hv2]; exact N.one_mem) hwwN
      apply hnoinv v hvS hv2
      have := N.inv_mem h1
      simpa using this
    exact four_le_orderOf H.base.S_pgroup hvS hv1 hv2
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * w * g = y) → IsExtremal S y → y ∈ N ∨ w⁻¹ * y ∈ N := by
    intro y hyS hconj _
    obtain ⟨g, hg⟩ := hconj
    by_cases hyN : y ∈ N
    · exact Or.inl hyN
    · right
      have hy2 : y * y = g⁻¹ * x * g := by
        rw [← hg, ← hww]; group
      by_cases hy2N : y * y ∈ N
      · have h1 := uniq_inv_coset Nd.normal Nd.g₀_mem Nd.cyc hyS hwS hyN Nd.w_not hy2N hwwN
        have := N.inv_mem h1
        simpa using this
      · exfalso
        have hy4 : (y * y) * (y * y) = 1 := by
          rw [hy2]
          calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
            _ = 1 := by rw [H.base.x_sq]; group
        have h1 := uniq_inv_coset Nd.normal Nd.g₀_mem Nd.cyc (S.mul_mem hyS hyS) hwS hy2N
          Nd.w_not (by rw [hy4]; exact N.one_mem) hwwN
        apply hnoinv (y * y) (S.mul_mem hyS hyS) hy4
        have := N.inv_mem h1
        simpa using this
  obtain ⟨g, hgN, hgext⟩ := transfer_conj H.IG H.base.simple H.base.nonabelian H.base.S_sylow
    Nd.le_S Nd.normal hne ⟨g₀, Nd.g₀_mem, Nd.cyc⟩ hwS Nd.w_not hord hext
  have hy2 : (g⁻¹ * w * g) * (g⁻¹ * w * g) = g⁻¹ * x * g := by
    rw [← hww]; group
  by_cases hyT : g⁻¹ * w * g ∈ T
  · exact B.noSq_Rd H A (Nd.inter _ hgN hyT) (g := g) hy2.symm
  · exact B.noSq_ST H A (Nd.le_S hgN) hyT (g := g) hy2.symm

end Ph1

end

end CFSG.GH74.GLS.Stage1.Thm6.Sec12b
