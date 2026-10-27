module

public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129P

open CFSG.Open Equiv

section Restrict

variable {α : Type*}

open scoped Classical in
noncomputable def restr (S : Set α) (x : Perm α) (h : ∀ j, x j ∈ S ↔ j ∈ S) : Perm α :=
  Perm.ofSubtype (x.subtypePerm (p := (· ∈ S)) h)

theorem restr_apply_of_mem {S : Set α} {x : Perm α} {h : ∀ j, x j ∈ S ↔ j ∈ S} {j : α}
    (hj : j ∈ S) : restr S x h j = x j := by
  classical
  exact Perm.ofSubtype_apply_of_mem (p := (· ∈ S)) (x.subtypePerm h) hj

theorem restr_apply_of_not_mem {S : Set α} {x : Perm α} {h : ∀ j, x j ∈ S ↔ j ∈ S} {j : α}
    (hj : j ∉ S) : restr S x h j = j := by
  classical
  exact Perm.ofSubtype_apply_of_not_mem (p := (· ∈ S)) (x.subtypePerm h) hj

theorem restr_pow_three {S : Set α} {z : Perm α} (hz : ∀ j, z j ∈ S ↔ j ∈ S) (h3 : z ^ 3 = 1) :
    restr S z hz ^ 3 = 1 := by
  ext j
  by_cases hj : j ∈ S
  · have h1 : z j ∈ S := (hz j).2 hj
    have h2 : z (z j) ∈ S := (hz _).2 h1
    have e4 : z (z (z j)) = j := by
      have := congrArg (fun f : Perm α => f j) h3
      simpa [pow_succ, Perm.mul_apply] using this
    simp [pow_succ, Perm.mul_apply, restr_apply_of_mem hj, restr_apply_of_mem h1,
      restr_apply_of_mem h2, e4]
  · simp [pow_succ, Perm.mul_apply, restr_apply_of_not_mem hj]

theorem restr_commute {S : Set α} {x z : Perm α} (hx : ∀ j, x j ∈ S ↔ j ∈ S)
    (hz : ∀ j, z j ∈ S ↔ j ∈ S) (hxz : x * z = z * x) :
    x * restr S z hz = restr S z hz * x := by
  ext j
  by_cases hj : j ∈ S
  · have hxj : x j ∈ S := (hx j).2 hj
    rw [Perm.mul_apply, Perm.mul_apply, restr_apply_of_mem hj, restr_apply_of_mem hxj]
    exact DFunLike.congr_fun hxz j
  · have hxj : x j ∉ S := fun h' => hj ((hx j).1 h')
    rw [Perm.mul_apply, Perm.mul_apply, restr_apply_of_not_mem hj, restr_apply_of_not_mem hxj]

end Restrict

theorem mem_alternatingGroup_of_pow_three {β : Type*} [DecidableEq β] [Fintype β] {τ : Perm β}
    (h : τ ^ 3 = 1) : τ ∈ alternatingGroup β := by
  rw [Perm.mem_alternatingGroup]
  have h1 : Perm.sign τ ^ 3 = 1 := by rw [← map_pow, h, map_one]
  have h2 : Perm.sign τ ^ 3 = Perm.sign τ := by
    rw [Int.units_pow_eq_pow_mod_two]; norm_num
  rw [← h2]; exact h1

theorem mem_of_maximal {n : ℕ} {X : Subgroup (Perm (Fin n))}
    (hX : X ≤ alternatingGroup (Fin n)) (hXel : IsElemAbelian 3 X)
    (hmax : ∀ Y : Subgroup (Perm (Fin n)), Y ≤ alternatingGroup (Fin n) →
      IsElemAbelian 3 Y → X ≤ Y → Y = X)
    {τ : Perm (Fin n)} (hτ3 : τ ^ 3 = 1) (hc : ∀ x ∈ X, x * τ = τ * x) : τ ∈ X := by
  have hτA : τ ∈ alternatingGroup (Fin n) := mem_alternatingGroup_of_pow_three hτ3
  have hY : X ⊔ Subgroup.zpowers τ = X := by
    refine hmax _ (sup_le hX (Subgroup.zpowers_le.2 hτA)) ?_ le_sup_left
    refine hXel.sup_of_commute (isElemAbelian_zpowers hτ3) fun a ha b hb => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_right (show Commute a τ from hc a ha) k).eq
  rw [← hY]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)

theorem eq_or_eq_of_card {G : Type*} [Group G] [Finite G] {p r : ℕ} (hp : p.Prime)
    {F K X : Subgroup G} (hFK : F ≤ K) (hKX : K ≤ X) (hF : Nat.card F = p ^ r)
    (hX : Nat.card X = p ^ (r + 1)) : K = F ∨ K = X := by
  have h1 : Nat.card K ∣ p ^ (r + 1) := hX ▸ Subgroup.card_dvd_of_le hKX
  obtain ⟨k, hk, hkK⟩ := (Nat.dvd_prime_pow hp).1 h1
  have h2 : p ^ r ∣ p ^ k := by
    rw [← hF, ← hkK]; exact Subgroup.card_dvd_of_le hFK
  have h3 : r ≤ k := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h2
  rcases (by omega : k = r ∨ k = r + 1) with rfl | rfl
  · left; exact (Subgroup.eq_of_le_of_card_ge hFK (by rw [hkK, hF])).symm
  · right; exact Subgroup.eq_of_le_of_card_ge hKX (by rw [hkK, hX])

theorem exists_moves {n : ℕ} {Ω₀ : Set (Fin n)} (hΩ₀ : Ω₀.ncard = 4)
    {X : Subgroup (Perm (Fin n))} (hX : X ≤ alternatingGroup (Fin n)) (hXel : IsElemAbelian 3 X)
    (hmax : ∀ Y : Subgroup (Perm (Fin n)), Y ≤ alternatingGroup (Fin n) →
      IsElemAbelian 3 Y → X ≤ Y → Y = X) :
    ∃ z ∈ X, ∃ a ∈ Ω₀, z a ≠ a := by
  by_contra hcon
  push Not at hcon
  obtain ⟨a, b, c, ha, hb, hc, hab, hac, hbc⟩ :=
    (Set.two_lt_ncard_iff (Set.toFinite Ω₀)).1 (by omega)
  have hτ3 : (swap a b * swap a c).IsThreeCycle := Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
  have hτo : (swap a b * swap a c) ^ 3 = 1 := by
    rw [← hτ3.orderOf]; exact pow_orderOf_eq_one _
  have hτfix : ∀ j, j ∉ Ω₀ → (swap a b * swap a c) j = j := by
    intro j hj
    have hja : j ≠ a := fun h => hj (h ▸ ha)
    have hjb : j ≠ b := fun h => hj (h ▸ hb)
    have hjc : j ≠ c := fun h => hj (h ▸ hc)
    rw [Perm.mul_apply, swap_apply_of_ne_of_ne hja hjc, swap_apply_of_ne_of_ne hja hjb]
  have hτX : swap a b * swap a c ∈ X := by
    refine mem_of_maximal hX hXel hmax hτo fun x hx => ?_
    have hd : Perm.Disjoint x (swap a b * swap a c) := fun j => by
      by_cases hj : j ∈ Ω₀
      · exact Or.inl (hcon x hx j hj)
      · exact Or.inr (hτfix j hj)
    exact hd.commute.eq
  have h1 := hcon _ hτX a ha
  rw [Perm.mul_apply, swap_apply_left, swap_apply_of_ne_of_ne hac.symm hbc.symm] at h1
  exact hac h1.symm

theorem permA {n r m : ℕ} (hr : 2 ≤ r) (hm : 0 < m) (hn : n = m * 3 ^ r + 4)
    (Ω₀ : Set (Fin n)) (hΩ₀ : Ω₀.ncard = 4)
    (F X : Subgroup (Equiv.Perm (Fin n)))
    (hFel : IsElemAbelian 3 F) (hFcard : Nat.card F = 3 ^ r)
    (hFfix : ∀ g ∈ F, ∀ j ∈ Ω₀, g j = j)
    (hFsemi : ∀ g ∈ F, g ≠ 1 → ∀ j, j ∉ Ω₀ → g j ≠ j)
    (hX : X ≤ alternatingGroup (Fin n)) (hXel : IsElemAbelian 3 X) (hFX : F ≤ X)
    (hXcard : Nat.card X = 3 ^ (r + 1))
    (hmax : ∀ Y : Subgroup (Equiv.Perm (Fin n)), Y ≤ alternatingGroup (Fin n) →
      IsElemAbelian 3 Y → X ≤ Y → Y = X) :
    m = 1 ∧ (∀ j k : Fin n, j ∉ Ω₀ → k ∉ Ω₀ → ∃! g : Equiv.Perm (Fin n), g ∈ F ∧ g j = k) ∧
      ∃ σ : Equiv.Perm (Fin n), σ.IsThreeCycle ∧ (∀ j, j ∉ Ω₀ → σ j = j) ∧
        X = F ⊔ Subgroup.zpowers σ ∧ F ⊓ Subgroup.zpowers σ = ⊥ := by
  classical
  have hFnt : ∃ g ∈ F, g ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hbot : F = ⊥ := (Subgroup.eq_bot_iff_forall F).2 hcon
    have h1 : Nat.card F = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [hFcard] at h1
    have : 1 < 3 ^ r := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  obtain ⟨g₀, hg₀F, hg₀1⟩ := hFnt
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => hXel.comm hx hy
  have hFc : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy => hFel.comm hx hy
  have hP1 : ∀ x ∈ X, ∀ j ∈ Ω₀, x j ∈ Ω₀ := by
    intro x hx j hj
    by_contra hxj
    apply hFsemi g₀ hg₀F hg₀1 (x j) hxj
    have hcomm := hXc g₀ (hFX hg₀F) x hx
    calc g₀ (x j) = (g₀ * x) j := rfl
      _ = (x * g₀) j := by rw [hcomm]
      _ = x (g₀ j) := rfl
      _ = x j := by rw [hFfix g₀ hg₀F j hj]
  have hP : ∀ x ∈ X, ∀ j, x j ∈ Ω₀ ↔ j ∈ Ω₀ := by
    intro x hx j
    refine ⟨fun h => ?_, hP1 x hx j⟩
    have := hP1 x⁻¹ (X.inv_mem hx) (x j) h
    simpa using this
  obtain ⟨σ, hσ3, hσX, hσfix, a, haΩ, hσa⟩ : ∃ σ : Perm (Fin n), σ ^ 3 = 1 ∧ σ ∈ X ∧
      (∀ j, j ∉ Ω₀ → σ j = j) ∧ ∃ a ∈ Ω₀, σ a ≠ a := by
    obtain ⟨z, hzX, a, haΩ, hza⟩ := exists_moves hΩ₀ hX hXel hmax
    have hz3 : z ^ 3 = 1 := hXel.2 z hzX
    have hzP := hP z hzX
    refine ⟨restr Ω₀ z hzP, restr_pow_three hzP hz3, ?_, fun j hj => restr_apply_of_not_mem hj,
      a, haΩ, ?_⟩
    · exact mem_of_maximal hX hXel hmax (restr_pow_three hzP hz3) fun x hx =>
        restr_commute (hP x hx) hzP (hXc x hx z hzX)
    · rw [restr_apply_of_mem haΩ]; exact hza
  have hσF : σ ∉ F := fun h => hσa (hFfix σ h a haΩ)
  have hσ1 : σ ≠ 1 := fun h => hσa (by rw [h]; rfl)
  have hσord : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hσ3c : σ.IsThreeCycle := by
    have hprime : (orderOf σ).Prime := by rw [hσord]; exact Nat.prime_three
    obtain ⟨k, hk⟩ := Perm.cycleType_prime_order hprime
    have hsupp : σ.support.card ≤ 4 := by
      calc σ.support.card = (σ.support : Set (Fin n)).ncard := (Set.ncard_coe_finset _).symm
        _ ≤ Ω₀.ncard := Set.ncard_le_ncard (fun j hj => by
            by_contra h
            exact (Perm.mem_support.1 (Finset.mem_coe.1 hj)) (hσfix j h)) (Set.toFinite _)
        _ = 4 := hΩ₀
    have hcard : σ.support.card = σ.cycleType.sum := (Perm.sum_cycleType σ).symm
    rw [hk, hσord, Multiset.sum_replicate, smul_eq_mul] at hcard
    have hk0 : k = 0 := by omega
    subst hk0
    rw [Perm.IsThreeCycle, hk, hσord]
    rfl
  have hXeq : X = F ⊔ Subgroup.zpowers σ := by
    have hle : F ⊔ Subgroup.zpowers σ ≤ X := sup_le hFX (Subgroup.zpowers_le.2 hσX)
    rcases eq_or_eq_of_card Nat.prime_three (le_sup_left : F ≤ F ⊔ Subgroup.zpowers σ) hle
      hFcard hXcard with h | h
    · exfalso
      have hmem : σ ∈ F ⊔ Subgroup.zpowers σ := Subgroup.mem_sup_right (Subgroup.mem_zpowers σ)
      rw [h] at hmem
      exact hσF hmem
    · exact h.symm
  have hinf : F ⊓ Subgroup.zpowers σ = ⊥ := by
    have hdvd : Nat.card ↥(F ⊓ Subgroup.zpowers σ) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_right : F ⊓ Subgroup.zpowers σ ≤ Subgroup.zpowers σ)
      rwa [Nat.card_zpowers, hσord] at this
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h3
    · exact Subgroup.card_eq_one.1 h1
    · exfalso
      have heq : F ⊓ Subgroup.zpowers σ = Subgroup.zpowers σ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, Nat.card_zpowers, hσord])
      have hmem : σ ∈ F ⊓ Subgroup.zpowers σ := by rw [heq]; exact Subgroup.mem_zpowers σ
      exact hσF hmem.1
  have hKF : ∀ x ∈ X, (∀ j ∈ Ω₀, x j = j) → x ∈ F := by
    intro x hx hxfix
    let Kst : Subgroup (Perm (Fin n)) := X ⊓ fixingSubgroup (Perm (Fin n)) Ω₀
    have hmemK : ∀ y, y ∈ Kst ↔ y ∈ X ∧ ∀ j ∈ Ω₀, y j = j := fun y => by
      simp [Kst, mem_fixingSubgroup_iff]
    have hFK : F ≤ Kst := fun g hg => (hmemK g).2 ⟨hFX hg, hFfix g hg⟩
    rcases eq_or_eq_of_card Nat.prime_three hFK (inf_le_left : Kst ≤ X) hFcard hXcard with h | h
    · have hxK : x ∈ Kst := (hmemK x).2 ⟨hx, hxfix⟩
      rw [h] at hxK
      exact hxK
    · exfalso
      have hσK : σ ∈ Kst := by rw [h]; exact hσX
      exact hσa (((hmemK σ).1 hσK).2 a haΩ)
  have hΩ1 : (Ω₀ᶜ).ncard = m * 3 ^ r := by
    rw [Set.ncard_compl, hΩ₀, Nat.card_eq_fintype_card, Fintype.card_fin, hn, Nat.add_sub_cancel]
  have hm1 : m = 1 := by
    by_contra hm1
    have hm2 : 2 ≤ m := by omega
    have hpos : 0 < (Ω₀ᶜ).ncard := by rw [hΩ1]; positivity
    obtain ⟨j₁, hj₁⟩ : ∃ j, j ∉ Ω₀ := by
      by_contra hcon
      push Not at hcon
      have : Ω₀ᶜ = ∅ := by ext j; simp [hcon j]
      rw [this] at hpos
      simp at hpos
    obtain ⟨O, hO⟩ : ∃ O : Set (Fin n), O = Set.range (fun g : F => (g : Perm (Fin n)) j₁) :=
      ⟨_, rfl⟩
    have hOcard : O.ncard ≤ 3 ^ r := by
      rw [← hFcard, ← Nat.card_coe_set_eq, hO]
      exact Finite.card_range_le _
    have hOmem : ∀ j, j ∈ O ↔ ∃ g ∈ F, g j₁ = j := by
      intro j
      rw [hO]
      constructor
      · rintro ⟨g, rfl⟩
        exact ⟨g, g.2, rfl⟩
      · rintro ⟨g, hg, rfl⟩
        exact ⟨⟨g, hg⟩, rfl⟩
    have hOinv : ∀ g ∈ F, ∀ j, g j ∈ O ↔ j ∈ O := by
      intro g hg j
      rw [hOmem, hOmem]
      constructor
      · rintro ⟨h, hh, hhj⟩
        refine ⟨g⁻¹ * h, F.mul_mem (F.inv_mem hg) hh, ?_⟩
        rw [Perm.mul_apply, hhj]
        simp
      · rintro ⟨h, hh, rfl⟩
        exact ⟨g * h, F.mul_mem hg hh, by rw [Perm.mul_apply]⟩
    have hOΩ : ∀ j ∈ O, j ∉ Ω₀ := by
      intro j hj hjΩ
      obtain ⟨g, hg, rfl⟩ := (hOmem j).1 hj
      have h1 := hFfix g⁻¹ (F.inv_mem hg) (g j₁) hjΩ
      apply hj₁
      have : j₁ = g j₁ := by simpa using h1
      rw [this]
      exact hjΩ
    obtain ⟨j₂, hj₂Ω, hj₂O⟩ : ∃ j, j ∉ Ω₀ ∧ j ∉ O := by
      by_contra hcon
      push Not at hcon
      have hsub : Ω₀ᶜ ⊆ O := fun j hj => hcon j hj
      have h1 := Set.ncard_le_ncard hsub (Set.toFinite O)
      rw [hΩ1] at h1
      have h2 := Nat.mul_le_mul_right (3 ^ r) hm2
      have h3 : 0 < 3 ^ r := by positivity
      omega
    have hg₀O := hOinv g₀ hg₀F
    obtain ⟨u, hu3, huF, huO, huO'⟩ : ∃ u : Perm (Fin n), u ^ 3 = 1 ∧ (∀ g ∈ F, g * u = u * g) ∧
        (∀ j, j ∉ O → u j = j) ∧ (∀ j ∈ O, u j = g₀ j) :=
      ⟨restr O g₀ hg₀O, restr_pow_three hg₀O (hFel.2 g₀ hg₀F),
        fun g hg => restr_commute (hOinv g hg) hg₀O (hFc g hg g₀ hg₀F),
        fun j hj => restr_apply_of_not_mem hj, fun j hj => restr_apply_of_mem hj⟩
    have huσ : σ * u = u * σ := by
      refine (Perm.Disjoint.commute ?_).eq
      intro j
      by_cases hj : j ∈ Ω₀
      · exact Or.inr (huO j (fun hjO => hOΩ j hjO hj))
      · exact Or.inl (hσfix j hj)
    have huX : ∀ x ∈ X, x * u = u * x := by
      intro x hx
      have hcent : X ≤ Subgroup.centralizer {u} := by
        rw [hXeq]
        refine sup_le (fun g hg => ?_) (Subgroup.zpowers_le.2 ?_)
        · exact Subgroup.mem_centralizer_singleton_iff.2 (huF g hg)
        · exact Subgroup.mem_centralizer_singleton_iff.2 huσ
      exact Subgroup.mem_centralizer_singleton_iff.1 (hcent hx)
    have huXm : u ∈ X := mem_of_maximal hX hXel hmax hu3 huX
    have huFmem : u ∈ F := hKF u huXm (fun j hj => huO j (fun hjO => hOΩ j hjO hj))
    have hu1 : u = 1 := by
      by_contra hne
      exact hFsemi u huFmem hne j₂ hj₂Ω (huO j₂ hj₂O)
    have hj₁O : j₁ ∈ O := (hOmem j₁).2 ⟨1, F.one_mem, rfl⟩
    have h1 := huO' j₁ hj₁O
    rw [hu1, Perm.one_apply] at h1
    exact hFsemi g₀ hg₀F hg₀1 j₁ hj₁ h1.symm
  have hΩ1' : (Ω₀ᶜ).ncard = 3 ^ r := by rw [hΩ1, hm1, one_mul]
  have hsemi' : ∀ g ∈ F, ∀ g' ∈ F, ∀ j, j ∉ Ω₀ → g j = g' j → g = g' := by
    intro g hg g' hg' j hj h
    by_contra hne
    have h1 : g'⁻¹ * g ≠ 1 := fun h1 => hne (inv_mul_eq_one.1 h1).symm
    refine hFsemi (g'⁻¹ * g) (F.mul_mem (F.inv_mem hg') hg) h1 j hj ?_
    rw [Perm.mul_apply, h]
    simp
  have hFpres : ∀ g ∈ F, ∀ j, j ∉ Ω₀ → g j ∉ Ω₀ := by
    intro g hg j hj hgj
    apply hj
    have h1 := hFfix g⁻¹ (F.inv_mem hg) (g j) hgj
    have : j = g j := by simpa using h1
    rw [this]
    exact hgj
  have hreg : ∀ j k : Fin n, j ∉ Ω₀ → k ∉ Ω₀ → ∃! g : Perm (Fin n), g ∈ F ∧ g j = k := by
    intro j k hj hk
    let φ : F → ↥(Ω₀ᶜ) := fun g => ⟨(g : Perm (Fin n)) j, hFpres g g.2 j hj⟩
    have hinj : Function.Injective φ := by
      intro g g' h
      exact Subtype.ext (hsemi' g g.2 g' g'.2 j hj (congrArg Subtype.val h))
    have hbij : Function.Bijective φ :=
      hinj.bijective_of_nat_card_le (by rw [Nat.card_coe_set_eq, hΩ1', hFcard])
    obtain ⟨g, hg⟩ := hbij.2 ⟨k, hk⟩
    refine ⟨g, ⟨g.2, congrArg Subtype.val hg⟩, ?_⟩
    rintro g' ⟨hg'F, hg'⟩
    exact hsemi' g' hg'F g g.2 j hj (hg'.trans (congrArg Subtype.val hg).symm)
  exact ⟨hm1, hreg, σ, hσ3c, hσfix, hXeq, hinf⟩

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129P

end
