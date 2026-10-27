module

public import CFSG.LocalAnalysis.GLTheoremA.S3.KMFive
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMGroup
public import CFSG.LocalAnalysis.GLTheoremA.S3.KMThree

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S3.KM

open CFSG.Open Subgroup
open CFSG.RankThree.PartTwo.Sec3 (squares)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A T : Subgroup G}
  {S H : Subgroup G} {b : G}

theorem card_zpowers_involution {z : G} (hz1 : z ≠ 1) (hzz : z * z = 1) :
    Nat.card (zpowers z) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz1

theorem Ctx.cent_le_pair (c : Ctx p A T) (a : Atom p A T b S H) {z : G} (hz : Extra S z)
    (hS32 : Nat.card S = 32)
    (hno : ∀ b' ∈ H, ∀ x ∈ T ⊓ centralizer (S : Set G), b' * x = x * b') :
    ∀ x ∈ T ⊓ centralizer (S : Set G), x = 1 ∨ x = z := by
  classical
  intro x hx
  by_contra hcon
  push Not at hcon
  obtain ⟨hx1, hxz⟩ := hcon
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz.z2
  have hST : S ≤ T := a.le
  obtain ⟨n, hn1, hnz, hn2⟩ := exists_pow_sq_mem c.two (mem_inf.1 hx).1 hx1 hxz
  set c₁ := x ^ n with hc₁
  have hc₁C : c₁ ∈ T ⊓ centralizer (S : Set G) := pow_mem hx n
  obtain ⟨P, hPS, hzP, hPc, hPcard⟩ := hz.exists_maxAbelian
  have hP8 : Nat.card P = 8 := by
    have : Nat.card P * Nat.card P = 8 * 8 := by omega
    exact Nat.mul_self_inj.1 this
  have hzc : c₁ * z = z * c₁ := (mem_centralizer_iff.1 (mem_inf.1 hc₁C).2 z hz.zS).symm
  have hcomm1 : ∀ u ∈ zpowers c₁, ∀ v ∈ zpowers z, u * v = v * u := by
    intro u hu v hv
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
    exact (Commute.zpow_zpow (show Commute c₁ z from hzc) i j).eq
  set Y := zpowers c₁ ⊔ zpowers z with hY
  have hYc : ∀ u ∈ Y, ∀ v ∈ Y, u * v = v * u :=
    comm_sup_of_commuting (comm_zpowers c₁) (comm_zpowers z) hcomm1
  have hYs : ∀ u ∈ Y, u ^ 2 = 1 ∨ u ^ 2 = z := by
    intro u hu
    obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := mem_sup_of_commuting hcomm1 u hu
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu₁
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hu₂
    rw [Commute.mul_pow (hcomm1 _ hu₁ _ hu₂) 2]
    have h1 : (z ^ j) ^ 2 = 1 := by
      rcases zpow_mem_pair hzz j with h | h
      · rw [h]; simp
      · rw [h, pow_two, hzz]
    rw [h1, mul_one]
    have h2 : (c₁ ^ i) ^ 2 = (c₁ ^ 2) ^ i := by
      rw [← zpow_natCast, ← zpow_natCast c₁ 2, ← zpow_mul, ← zpow_mul, mul_comm]
    rw [h2]
    rcases hn2 with h | h
    · left; rw [h, one_zpow]
    · rcases zpow_mem_pair hzz i with h' | h'
      · left; rw [h, h']
      · right; rw [h, h']
  have hYS : Y ≤ centralizer (S : Set G) := by
    refine sup_le (zpowers_le.2 (mem_inf.1 hc₁C).2) (zpowers_le.2 ?_)
    rw [mem_centralizer_iff]
    intro s hs
    exact (hz.z_central s hs).symm
  have hPY : ∀ u ∈ P, ∀ v ∈ Y, u * v = v * u := fun u hu v hv =>
    mem_centralizer_iff.1 (hYS hv) u (hPS hu)
  have hPYcard : Nat.card (P ⊓ Y : Subgroup G) ≤ 2 := by
    have hle : P ⊓ Y ≤ zpowers z := by
      intro y hy
      obtain ⟨hyP, hyY⟩ := mem_inf.1 hy
      have := (hz.center y (hPS hyP)).1 (fun s hs => (mem_centralizer_iff.1 (hYS hyY) s hs).symm)
      rcases this with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    have := Subgroup.card_le_of_le hle
    rw [card_zpowers_involution hz.z1 hzz] at this
    exact this
  obtain ⟨V, hVle, hVe, hVcard⟩ := exists_elemAbelian_of_commuting hzz hPc hYc hPY
    (fun u hu => hz.sq_mem u (hPS hu)) hYs hPYcard
  have hY4 : 4 ≤ Nat.card Y := by
    have hlt : zpowers z < Y := by
      refine lt_of_le_of_ne le_sup_right fun heq => ?_
      have hc₁Y : c₁ ∈ Y := (le_sup_left : zpowers c₁ ≤ Y) (mem_zpowers c₁)
      rw [← heq] at hc₁Y
      obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hc₁Y
      rcases zpow_mem_pair hzz i with h | h
      · exact hn1 (by rw [← hi, h])
      · exact hnz (by rw [← hi, h])
    have := card_ge_of_lt hlt
    rw [card_zpowers_involution hz.z1 hzz] at this
    omega
  have hHc : ∀ y ∈ T ⊓ centralizer (S : Set G), y ∈ T ⊓ centralizer (H : Set G) := by
    intro y hy
    exact mem_inf.2 ⟨(mem_inf.1 hy).1, mem_centralizer_iff.2 (fun h hh => hno h hh y hy)⟩
  have hVT : V ≤ T ⊓ centralizer (H : Set G) := by
    refine hVle.trans (sup_le ?_ (sup_le ?_ ?_))
    · intro u hu
      exact mem_inf.2 ⟨hST (hPS hu), mem_centralizer_iff.2 (fun h hh => a.cent u (hPS hu) h hh)⟩
    · exact zpowers_le.2 (hHc c₁ hc₁C)
    · exact zpowers_le.2 (mem_inf.2 ⟨hST hz.zS, mem_centralizer_iff.2
        (fun h hh => a.cent z hz.zS h hh)⟩)
  have := c.rank1 a.hyp hVT hVe
  rw [hP8] at hVcard
  omega

theorem Ctx.normalizer_le (c : Ctx p A T) (a : Atom p A T b S H) {z : G} (hz : Extra S z)
    (hFz : ∀ f ∈ squares S, f = 1 ∨ f = z)
    (hCz : ∀ x ∈ T ⊓ centralizer (S : Set G), x = 1 ∨ x = z) :
    ∀ t ∈ T, t ∈ normalizer (S : Set G) → t ∈ S := by
  classical
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz.z2
  set K : Subgroup G := T ⊓ normalizer (S : Set G) with hK
  have hKT : K ≤ T := inf_le_left
  have hKnS : K ≤ normalizer (S : Set G) := inf_le_right
  have hSK : S ≤ K := le_inf a.le le_normalizer
  have hAX : A ≤ normalizer ((zpowers b : Subgroup G) : Set G) :=
    le_normalizer_zpowers_of_comm (fun x hx y hy => c.comm hx hy) a.hb
  have hKn : A ≤ normalizer (K : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro k hk
    refine mem_inf.2 ⟨?_, ?_⟩
    · exact (mem_normalizer_iff.1 (c.norm hg) k).1 (mem_inf.1 hk).1
    · have hgS : g ∈ normalizer (S : Set G) := a.inv hg
      have hkS : k ∈ normalizer (S : Set G) := (mem_inf.1 hk).2
      exact mul_mem (mul_mem hgS hkS) (inv_mem hgS)
  have hM : ⁅S, K⁆ ≤ zpowers z := by
    by_contra hMn
    set M := ⁅S, K⁆ with hMdef
    have hMS : M ≤ S := le_normalizer_iff_commutator_le_left.mp hKnS
    have hAM : A ≤ normalizer (M : Set G) := commutator_mem_normalizer a.inv hKn
    have hM2 : IsPGroup 2 M := c.two.to_le (hMS.trans a.le)
    have hXM : zpowers b ≤ normalizer (M : Set G) := (zpowers_le.2 a.hb).trans hAM
    have hM₁ne : ⁅M, zpowers b⁆ ≠ ⊥ := by
      intro hbot
      apply hMn
      intro m hm
      have hcen := commutator_eq_bot_iff_le_centralizer.1 hbot hm
      have hbm : b * m = m * b := mem_centralizer_iff.1 hcen b (mem_zpowers b)
      rcases hFz m (a.mem_squares_of_comm (hMS hm) hbm) with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    have hM₁M : ⁅M, zpowers b⁆ ≤ M := le_normalizer_iff_commutator_le_left.mp hXM
    have hM₁ := a.min ⁅M, zpowers b⁆ (hM₁M.trans hMS) (a.idem hM2 hAM) hM₁ne
    have hSM : S ≤ M := by
      rw [← hM₁]
      exact hM₁M
    have hMS' : M = S := le_antisymm hMS hSM
    exact a.ne (eq_bot_of_commutator_eq_self (c.two.to_le hKT) hSK hMS')
  intro t htT htn
  have htK : t ∈ K := mem_inf.2 ⟨htT, htn⟩
  have hcomm : ∀ s ∈ S, t * s = s * t ∨ t * s = z * s * t := by
    intro s hs
    have h1 : ⁅s, t⁆ ∈ zpowers z := hM (commutator_mem_commutator hs htK)
    have h2 : ⁅t, s⁆ ∈ zpowers z := by
      rw [← commutatorElement_inv]
      exact inv_mem h1
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 h2
    rcases zpow_mem_pair hzz i with h | h
    · left
      rw [h] at hi
      exact commutatorElement_eq_one_iff_mul_comm.1 hi.symm
    · right
      rw [h] at hi
      calc t * s = (t * s * t⁻¹ * s⁻¹) * s * t := by group
        _ = z * s * t := by
          rw [show t * s * t⁻¹ * s⁻¹ = ⁅t, s⁆ from rfl, ← hi]
  obtain ⟨s₀, hs₀, hinner⟩ := hz.exists_inner hcomm
  have hu : t * s₀⁻¹ ∈ T ⊓ centralizer (S : Set G) :=
    mem_inf.2 ⟨T.mul_mem htT (T.inv_mem (a.le hs₀)),
      mem_centralizer_iff.2 (fun s hs => (hinner s hs).symm)⟩
  have hSz : ∀ x ∈ T ⊓ centralizer (S : Set G), x ∈ S := by
    intro x hx
    rcases hCz x hx with h | h
    · rw [h]; exact one_mem _
    · rw [h]; exact hz.zS
  have : t = (t * s₀⁻¹) * s₀ := by group
  rw [this]
  exact S.mul_mem (hSz _ hu) hs₀

theorem Ctx.exists_noncomm_cent (c : Ctx p A T) (a : Atom p A T b S H) {z : G}
    (hz : Extra S z) (hS32 : Nat.card S = 32) (hFz : ∀ f ∈ squares S, f = 1 ∨ f = z) :
    ∃ b' ∈ H, ∃ x ∈ T ⊓ centralizer (S : Set G), b' * x ≠ x * b' := by
  by_contra hno
  push Not at hno
  have hCz := c.cent_le_pair a hz hS32 hno
  have hN := c.normalizer_le a hz hFz hCz
  have hTS : T ≤ S := le_of_normalizer_le c.two a.le hN
  obtain ⟨h, hh, h1⟩ := c.hyp_exists_ne_one a.hyp
  apply h1
  apply c.faithful h (a.hyp.1 hh)
  intro t ht
  exact a.cent t (hTS ht) h hh

theorem Ctx.false_of_five (c : Ctx p A T) (hp5 : 5 ≤ p) : False := by
  classical
  obtain ⟨b, hbA, hb1⟩ := c.exists_ne_one
  obtain ⟨t, htT, htb⟩ := c.exists_noncomm hbA hb1
  obtain ⟨S₁, H₁, a₁⟩ := exists_atom c.prime c.odd c.elem c.two c.norm hbA ⟨t, htT, htb⟩
  obtain ⟨z, hz, hzA, hS32, -, hFz⟩ := a₁.extra5 c hp5 le_rfl
  obtain ⟨b', hb'H, x, hx, hne⟩ := c.exists_noncomm_cent a₁ hz hS32 hFz
  have hb'A : b' ∈ A := a₁.hyp.1 hb'H
  have hzz : z * z = 1 := by rw [← pow_two]; exact hz.z2
  set C := T ⊓ centralizer (S₁ : Set G) with hC
  have hCn : A ≤ normalizer (C : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    intro k hk
    obtain ⟨hkT, hkC⟩ := mem_inf.1 hk
    refine mem_inf.2 ⟨(mem_normalizer_iff.1 (c.norm hg) k).1 hkT, mem_centralizer_iff.2 ?_⟩
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S₁ := by
      have := (mem_normalizer_iff.1 (a₁.inv (inv_mem hg)) s).1 hs
      simpa using this
    have h1 := mem_centralizer_iff.1 hkC _ hs'
    calc s * (g * k * g⁻¹) = g * ((g⁻¹ * s * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * k * g⁻¹ * s := by group
  have hC2 : IsPGroup 2 C := c.two.to_le inf_le_left
  obtain ⟨S₂, H₂, a₂⟩ := exists_atom c.prime c.odd c.elem hC2 hCn hb'A ⟨x, hx, hne⟩
  obtain ⟨z₂, hz₂, hz₂A, hS₂32, -, hFz₂⟩ := a₂.extra5 c hp5 inf_le_left
  have hS₂C : S₂ ≤ C := a₂.le
  have hST₁ : S₁ ≤ T := a₁.le
  have hST₂ : S₂ ≤ T := hS₂C.trans inf_le_left
  have hzz₂ : z₂ = z := by
    have hcom : ∀ u ∈ zpowers z, ∀ v ∈ zpowers z₂, u * v = v * u := by
      intro u hu v hv
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hu
      obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hv
      have h1 : z * z₂ = z₂ * z :=
        mem_centralizer_iff.1 (mem_inf.1 (hS₂C hz₂.zS)).2 z hz.zS
      exact (Commute.zpow_zpow (show Commute z z₂ from h1) i j).eq
    obtain ⟨hVe, -⟩ := isElemAbelian_sup_of_commuting (isElemAbelian_zpowers hz.z2)
      (isElemAbelian_zpowers hz₂.z2) hcom
    have hVA : zpowers z ⊔ zpowers z₂ ≤ T ⊓ centralizer (A : Set G) := by
      refine sup_le (zpowers_le.2 (mem_inf.2 ⟨hST₁ hz.zS, mem_centralizer_iff.2 hzA⟩))
        (zpowers_le.2 (mem_inf.2 ⟨hST₂ hz₂.zS, mem_centralizer_iff.2 hz₂A⟩))
    have h2 := c.rank0 hVA hVe
    exact eq_of_card_le_two h2 ((le_sup_right : zpowers z₂ ≤ zpowers z ⊔ zpowers z₂)
      (mem_zpowers z₂)) ((le_sup_left : zpowers z ≤ zpowers z ⊔ zpowers z₂) (mem_zpowers z))
      hz₂.z1 hz.z1
  have hz₂' : Extra S₂ z := hzz₂ ▸ hz₂
  obtain ⟨P₁, hP₁S, hzP₁, hP₁c, hP₁card⟩ := hz.exists_maxAbelian
  obtain ⟨P₂, hP₂S, hzP₂, hP₂c, hP₂card⟩ := hz₂'.exists_maxAbelian
  have hP₁8 : Nat.card P₁ = 8 := by
    have : Nat.card P₁ * Nat.card P₁ = 8 * 8 := by omega
    exact Nat.mul_self_inj.1 this
  have hP₂8 : Nat.card P₂ = 8 := by
    have : Nat.card P₂ * Nat.card P₂ = 8 * 8 := by omega
    exact Nat.mul_self_inj.1 this
  have hPP : ∀ u ∈ P₁, ∀ v ∈ P₂, u * v = v * u := fun u hu v hv =>
    mem_centralizer_iff.1 (mem_inf.1 (hS₂C (hP₂S hv))).2 u (hP₁S hu)
  have hP₁P₂card : Nat.card (P₁ ⊓ P₂ : Subgroup G) ≤ 2 := by
    have hle : P₁ ⊓ P₂ ≤ zpowers z := by
      intro y hy
      obtain ⟨hy₁, hy₂⟩ := mem_inf.1 hy
      have hyC := mem_centralizer_iff.1 (mem_inf.1 (hS₂C (hP₂S hy₂))).2
      have := (hz.center y (hP₁S hy₁)).1 (fun s hs => (hyC s hs).symm)
      rcases this with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers z
    have := Subgroup.card_le_of_le hle
    rw [card_zpowers_involution hz.z1 hzz] at this
    exact this
  obtain ⟨V, hVle, hVe, hVcard⟩ := exists_elemAbelian_of_commuting hzz hP₁c hP₂c hPP
    (fun u hu => hz.sq_mem u (hP₁S hu)) (fun u hu => hz₂'.sq_mem u (hP₂S hu)) hP₁P₂card
  have hne12 : H₁ ≠ H₂ := fun h => a₂.not_mem (h ▸ hb'H)
  have hcard : Nat.card (H₁ ⊓ H₂ : Subgroup G) * p ^ 2 = Nat.card A :=
    IsHyp.card_inf c.prime (fun x hx y hy => c.comm hx hy) a₁.hyp a₂.hyp hne12
  have hVT : V ≤ T ⊓ centralizer ((H₁ ⊓ H₂ : Subgroup G) : Set G) := by
    refine hVle.trans (sup_le ?_ ?_)
    · intro u hu
      exact mem_inf.2 ⟨hST₁ (hP₁S hu), mem_centralizer_iff.2 (fun h hh =>
        a₁.cent u (hP₁S hu) h (mem_inf.1 hh).1)⟩
    · intro u hu
      have hu₂ := hP₂S hu
      exact mem_inf.2 ⟨hST₂ hu₂, mem_centralizer_iff.2 (fun h hh =>
        a₂.cent u hu₂ h (mem_inf.1 hh).2)⟩
  have h8 := c.rank2 (inf_le_left.trans a₁.hyp.1) hcard hVT hVe
  rw [hP₁8, hP₂8] at hVcard
  omega

end CFSG.LocalAnalysis.GLTheoremA.S3.KM
