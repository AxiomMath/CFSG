module

public import CFSG.ClassicalInvolution.Q3.Q3TLT3Act
public import CFSG.ClassicalInvolution.Q3.Q3TLTDatum

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG CFSG.Open CFSG.ClassicalInvolution QuaternionGroup
open scoped commutatorElement

section Group

theorem orderOf_conj_eq {G : Type*} [Group G] (c g : G) : orderOf (c * g * c⁻¹) = orderOf g := by
  have := (MulAut.conj c).orderOf_eq g
  rwa [MulAut.conj_apply] at this

theorem eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four {N : Type*} [Group N] [Finite N] {y h : N}
    (hy : orderOf y = 4) (hh : orderOf h = 4) (hmem : y ∈ Subgroup.zpowers h) :
    y = h ∨ y = h⁻¹ := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, h ^ n = y :=
    (Submonoid.mem_powers_iff y h).mp (mem_powers_iff_mem_zpowers.mpr hmem)
  subst hn
  have h4 : h ^ 4 = 1 := by rw [← hh]; exact pow_orderOf_eq_one h
  have e : h ^ n = h ^ (n % 4) := by
    have := (pow_mod_orderOf h n).symm
    rwa [hh] at this
  have hlt : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [e] at hy ⊢
  generalize n % 4 = r at hy hlt ⊢
  interval_cases r
  · simp at hy
  · exact Or.inl (by simp)
  · exfalso
    rw [orderOf_pow' h (by norm_num), hh] at hy
    norm_num at hy
  · refine Or.inr (eq_inv_of_mul_eq_one_left ?_)
    rw [← pow_succ]
    exact h4

end Group

section Lift

variable {G : Type*} [Group G] [Finite G] {R S : Subgroup G} {t : G}

theorem tl3_exists_conj_mem_zpowers (hO : OddByQuat R S t) (hS8 : Nat.card S = 8)
    {g h c : G} (hh : h ∈ S) (hog : orderOf g = 4) (hoh : orderOf h = 4)
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) (hcg : c * g * c⁻¹ ∈ R)
    (hmem : (QuotientGroup.mk (⟨c * g * c⁻¹, hcg⟩ : R) : R ⧸ oddCore R) ∈
      Subgroup.zpowers (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R)) :
    ∃ c' ∈ Subgroup.centralizer ({t} : Set G), c' * g * c'⁻¹ ∈ Subgroup.zpowers h := by
  have hyo : orderOf (c * g * c⁻¹) = 4 := (orderOf_conj_eq c g).trans hog
  have hP2 : IsPGroup 2 (Subgroup.zpowers (c * g * c⁻¹)) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hyo]; norm_num)
  have hPR : Subgroup.zpowers (c * g * c⁻¹) ≤ R := Subgroup.zpowers_le.mpr hcg
  obtain ⟨P', hP'syl, hPP'⟩ := exists_isSylow2Of_ge hP2 hPR
  obtain ⟨r, hr, hP'eq⟩ := hO.sylow.exists_conj hP'syl
  have hyP' : c * g * c⁻¹ ∈ P' := hPP' (Subgroup.mem_zpowers _)
  rw [hP'eq, mem_conjSubgroup_iff] at hyP'
  have hrC : r ∈ Subgroup.centralizer ({t} : Set G) := hO.le_C hr
  refine ⟨r⁻¹ * c, Subgroup.mul_mem _ (Subgroup.inv_mem _ hrC) hc, ?_⟩
  have hg'eq : (r⁻¹ * c) * g * (r⁻¹ * c)⁻¹ = r⁻¹ * (c * g * c⁻¹) * r := by group
  rw [hg'eq]
  have hι := hO.bijective_restrict
  set ι : S →* R ⧸ oddCore R :=
    (QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion hO.S_le) with hιdef
  let ιe : S ≃* R ⧸ oddCore R := MulEquiv.ofBijective ι hι
  have hQ8 : Nat.card (R ⧸ oddCore R) = 8 := by rw [← Nat.card_congr ιe.toEquiv]; exact hS8
  have hqo : orderOf (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R) = 4 := by
    have : (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R) = ιe ⟨h, hh⟩ := rfl
    rw [this, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
    exact hoh
  have hidx : (Subgroup.zpowers
      (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R)).index = 2 := by
    have := Subgroup.card_mul_index (Subgroup.zpowers
      (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R))
    rw [Nat.card_zpowers, hqo, hQ8] at this
    omega
  have hnorm := Subgroup.normal_of_index_eq_two hidx
  let g'S : S := ⟨r⁻¹ * (c * g * c⁻¹) * r, hyP'⟩
  have hcls : ι g'S = (QuotientGroup.mk (⟨r, hr⟩ : R) : R ⧸ oddCore R)⁻¹ *
      QuotientGroup.mk (⟨c * g * c⁻¹, hcg⟩ : R) * QuotientGroup.mk (⟨r, hr⟩ : R) := by
    rw [← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    rfl
  have hmem' : ι g'S ∈ Subgroup.zpowers
      (QuotientGroup.mk (⟨h, hO.S_le hh⟩ : R) : R ⧸ oddCore R) := by
    rw [hcls]
    have := hnorm.conj_mem _ hmem (QuotientGroup.mk (⟨r, hr⟩ : R) : R ⧸ oddCore R)⁻¹
    simpa using this
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem'
  have hhn : h ^ n ∈ S := zpow_mem hh n
  have hinj : ι ⟨h ^ n, hhn⟩ = ι g'S := by
    have e1 : (⟨h ^ n, hhn⟩ : S) = (⟨h, hh⟩ : S) ^ n := Subtype.ext (by simp)
    rw [e1, map_zpow]
    exact hn
  have hval : h ^ n = r⁻¹ * (c * g * c⁻¹) * r := congrArg Subtype.val (hι.1 hinj)
  rw [← hval]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers h) n

end Lift

section Datum

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

namespace TightDatum

@[expose] noncomputable def act (d : TightDatum R S t) :
    Subgroup.centralizer ({t} : Set G) →* MulAut (R ⧸ oddCore R) :=
  (tl3Act R).comp (Subgroup.inclusion d.le_normalizer)

theorem act_mk (d : TightDatum R S t) {c : G} (hc : c ∈ Subgroup.centralizer ({t} : Set G))
    {g : G} (hg : g ∈ R) (hcg : c * g * c⁻¹ ∈ R) :
    d.act ⟨c, hc⟩ (QuotientGroup.mk ⟨g, hg⟩) = QuotientGroup.mk ⟨c * g * c⁻¹, hcg⟩ := by
  unfold act
  rw [MonoidHom.comp_apply, tl3Act_mk]
  rfl

theorem act_eq_one_iff (d : TightDatum R S t) {c : G}
    (hc : c ∈ Subgroup.centralizer ({t} : Set G)) :
    d.act ⟨c, hc⟩ = 1 ↔ ∀ r ∈ R, ⁅c, r⁆ ∈ oddCoreImg R :=
  tl3Act_eq_one_iff R ⟨c, d.le_normalizer hc⟩

omit [Finite G] in
theorem conj_mem (d : TightDatum R S t) {c : G} (hc : c ∈ Subgroup.centralizer ({t} : Set G))
    {g : G} (hg : g ∈ R) : c * g * c⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.mp (d.le_normalizer hc) g).mp hg

end TightDatum

end Datum

section Main

variable {G : Type*} [Group G] [Finite G] {R : Subgroup G} {S : Sylow 2 R} {t : G}

theorem TightDatum.threeAct_iff_fusion (d : TightDatum R S t)
    (hS8 : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2)) :
    (∃ (x : G) (k : ℕ), x ∈ Subgroup.centralizer ({t} : Set G) ∧ x ^ 3 ^ k = 1 ∧
      ∃ r ∈ R, ⁅x, r⁆ ∉ oddCoreImg R) ↔
    ∀ Z₁ Z₂ : Subgroup G, Z₁ ≤ (S : Subgroup R).map R.subtype →
      Z₂ ≤ (S : Subgroup R).map R.subtype → IsCyclic Z₁ → Nat.card Z₁ = 4 → IsCyclic Z₂ →
      Nat.card Z₂ = 4 →
      ∃ c ∈ Subgroup.centralizer ({t} : Set G), Z₁.map (MulAut.conj c).toMonoidHom = Z₂ := by
  obtain ⟨eS⟩ := hS8
  have hO : OddByQuat R ((S : Subgroup R).map R.subtype) t :=
    OddByQuat.of_quaternion S d.quat d.mem d.order d.cent d.normal d.twoGroup
  set S' : Subgroup G := (S : Subgroup R).map R.subtype with hS'
  let eS' : ↥S' ≃* QuaternionGroup 2 :=
    (Subgroup.equivMapOfInjective (S : Subgroup R) R.subtype R.subtype_injective).symm.trans eS
  have hS'8 : Nat.card S' = 8 := by
    rw [Nat.card_congr eS'.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hι := hO.bijective_restrict
  set ι : ↥S' →* R ⧸ oddCore R :=
    (QuotientGroup.mk' (oddCore R)).comp (Subgroup.inclusion hO.S_le) with hιdef
  let eQ : (R ⧸ oddCore R) ≃* QuaternionGroup 2 := (MulEquiv.ofBijective ι hι).symm.trans eS'
  have hord : ∀ s : ↥S', orderOf (ι s) = orderOf (s : G) := fun s => by
    rw [orderOf_injective ι hι.1 s, Subgroup.orderOf_coe]
  constructor
  · rintro ⟨x, k, hxC, hx3, r, hr, hxr⟩ Z₁ Z₂ hZ₁ hZ₂ cyc₁ card₁ cyc₂ card₂
    obtain ⟨g, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Z₁).mp cyc₁
    obtain ⟨h, rfl⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Z₂).mp cyc₂
    have hog : orderOf g = 4 := by rw [← Nat.card_zpowers]; exact card₁
    have hoh : orderOf h = 4 := by rw [← Nat.card_zpowers]; exact card₂
    have hgS : g ∈ S' := hZ₁ (Subgroup.mem_zpowers g)
    have hhS : h ∈ S' := hZ₂ (Subgroup.mem_zpowers h)
    have hgR : g ∈ R := hO.S_le hgS
    have hhR : h ∈ R := hO.S_le hhS
    have hgq : orderOf (QuotientGroup.mk (⟨g, hgR⟩ : R) : R ⧸ oddCore R) = 4 :=
      (hord ⟨g, hgS⟩).trans hog
    have hhq : orderOf (QuotientGroup.mk (⟨h, hhR⟩ : R) : R ⧸ oddCore R) = 4 :=
      (hord ⟨h, hhS⟩).trans hoh
    have hρ1 : d.act ⟨x, hxC⟩ ≠ 1 := fun h1 => hxr ((d.act_eq_one_iff hxC).mp h1 r hr)
    have hρk : d.act ⟨x, hxC⟩ ^ 3 ^ k = 1 := by
      rw [← map_pow]
      have : (⟨x, hxC⟩ : Subgroup.centralizer ({t} : Set G)) ^ 3 ^ k = 1 :=
        Subtype.ext (by simpa using hx3)
      rw [this, map_one]
    obtain ⟨m, hm, hmm⟩ := tl3_aut_transitive eQ hρk hρ1 hgq hhq
    have hcC : x ^ m ∈ Subgroup.centralizer ({t} : Set G) := Subgroup.pow_mem _ hxC m
    have hcg : x ^ m * g * (x ^ m)⁻¹ ∈ R := d.conj_mem hcC hgR
    have hact : (d.act ⟨x, hxC⟩ ^ m) (QuotientGroup.mk ⟨g, hgR⟩) =
        QuotientGroup.mk ⟨x ^ m * g * (x ^ m)⁻¹, hcg⟩ := by
      have h1 : d.act ⟨x ^ m, hcC⟩ = d.act ⟨x, hxC⟩ ^ m := by
        rw [← map_pow]
        rfl
      rw [← d.act_mk hcC hgR hcg, h1]
    have hmem : (QuotientGroup.mk (⟨x ^ m * g * (x ^ m)⁻¹, hcg⟩ : R) : R ⧸ oddCore R) ∈
        Subgroup.zpowers (QuotientGroup.mk (⟨h, hO.S_le hhS⟩ : R) : R ⧸ oddCore R) := by
      rw [← hact]
      rcases hmm with h0 | h0
      · rw [h0]
        exact Subgroup.mem_zpowers _
      · rw [h0]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    obtain ⟨c', hc'C, hc'mem⟩ := tl3_exists_conj_mem_zpowers hO hS'8 hhS hog hoh hcC hcg hmem
    refine ⟨c', hc'C, ?_⟩
    rw [MonoidHom.map_zpowers]
    have hmem' : (MulAut.conj c').toMonoidHom g ∈ Subgroup.zpowers h := by
      simpa [MulAut.conj_apply] using hc'mem
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem') ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hoh]
    exact le_of_eq ((MulEquiv.orderOf_eq (MulAut.conj c') g).trans hog).symm
  · intro hF
    obtain ⟨sa, hsa⟩ := hι.2 (eQ.symm (a 1))
    obtain ⟨sb, hsb⟩ := hι.2 (eQ.symm (xa 0))
    obtain ⟨sc, hsc⟩ := hι.2 (eQ.symm (xa 1))
    have hoa : orderOf (sa : G) = 4 := by
      rw [← hord, hsa, MulEquiv.orderOf_eq, orderOf_a_one]
    have hob : orderOf (sb : G) = 4 := by
      rw [← hord, hsb, MulEquiv.orderOf_eq, orderOf_xa]
    have hoc : orderOf (sc : G) = 4 := by
      rw [← hord, hsc, MulEquiv.orderOf_eq, orderOf_xa]
    have step : ∀ s s' : ↥S', orderOf (s : G) = 4 → orderOf (s' : G) = 4 →
        ∃ (c : G) (hc : c ∈ Subgroup.centralizer ({t} : Set G)),
          d.act ⟨c, hc⟩ (ι s) = ι s' ∨ d.act ⟨c, hc⟩ (ι s) = (ι s')⁻¹ := by
      intro s s' hs hs'
      obtain ⟨c, hc, hcZ⟩ := hF (Subgroup.zpowers (s : G)) (Subgroup.zpowers (s' : G))
        (Subgroup.zpowers_le.mpr s.2) (Subgroup.zpowers_le.mpr s'.2)
        ((Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨_, rfl⟩)
        (by rw [Nat.card_zpowers, hs])
        ((Subgroup.isCyclic_iff_exists_zpowers_eq_top _).mpr ⟨_, rfl⟩)
        (by rw [Nat.card_zpowers, hs'])
      refine ⟨c, hc, ?_⟩
      have hmem : c * (s : G) * c⁻¹ ∈ Subgroup.zpowers (s' : G) := by
        rw [← hcZ]
        exact Subgroup.mem_map.mpr ⟨(s : G), Subgroup.mem_zpowers _, by simp [MulAut.conj_apply]⟩
      have hsR : (s : G) ∈ R := hO.S_le s.2
      have hs'R : (s' : G) ∈ R := hO.S_le s'.2
      have hcs : c * (s : G) * c⁻¹ ∈ R := d.conj_mem hc hsR
      have hact := d.act_mk hc hsR hcs
      rcases eq_or_eq_inv_of_mem_zpowers_of_orderOf_eq_four
        ((orderOf_conj_eq c (s : G)).trans hs) hs' hmem with h0 | h0
      · left
        show d.act ⟨c, hc⟩ (QuotientGroup.mk ⟨(s : G), hsR⟩) = QuotientGroup.mk ⟨(s' : G), hs'R⟩
        rw [hact]
        exact congrArg QuotientGroup.mk (Subtype.ext h0)
      · right
        show d.act ⟨c, hc⟩ (QuotientGroup.mk ⟨(s : G), hsR⟩) =
          (QuotientGroup.mk ⟨(s' : G), hs'R⟩ : R ⧸ oddCore R)⁻¹
        rw [hact, ← QuotientGroup.mk_inv]
        exact congrArg QuotientGroup.mk (Subtype.ext h0)
    obtain ⟨c₁, hc₁, h₁⟩ := step sa sb hoa hob
    obtain ⟨c₂, hc₂, h₂⟩ := step sa sc hoa hoc
    rw [hsa, hsb] at h₁
    rw [hsa, hsc] at h₂
    have hex : ∃ (x : Subgroup.centralizer ({t} : Set G)) (k : ℕ),
        x ^ 3 ^ k = 1 ∧ d.act x ≠ 1 := by
      rcases tl3_aut_three eQ h₁ h₂ with h | h | h
      · obtain ⟨x, k, hx1, hx2⟩ :=
          exists_pow_three_pow_of_ne_one d.act (c := ⟨c₁, hc₁⟩) h.1 h.2
        exact ⟨x, k, hx1, hx2⟩
      · obtain ⟨x, k, hx1, hx2⟩ :=
          exists_pow_three_pow_of_ne_one d.act (c := ⟨c₂, hc₂⟩) h.1 h.2
        exact ⟨x, k, hx1, hx2⟩
      · obtain ⟨x, k, hx1, hx2⟩ :=
          exists_pow_three_pow_of_ne_one d.act (c := ⟨c₁, hc₁⟩ * ⟨c₂, hc₂⟩)
            (by rw [map_mul]; exact h.1) (by rw [map_mul]; exact h.2)
        exact ⟨x, k, hx1, hx2⟩
    obtain ⟨x, k, hxk, hx1⟩ := hex
    refine ⟨(x : G), k, x.2, by simpa using congrArg Subtype.val hxk, ?_⟩
    by_contra hcon
    push Not at hcon
    exact hx1 ((d.act_eq_one_iff x.2).mpr hcon)

end Main

end CFSG.ClassicalInvolution.Q3
