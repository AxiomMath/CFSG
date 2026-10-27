module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Foote.E27

section KerComp

variable {A B C : Type*} [AddGroup A] [AddGroup B] [AddGroup C]

theorem card_ker_comp_le [Finite A] [Finite B] (f : B →+ C) (g : A →+ B) :
    Nat.card (f.comp g).ker ≤ Nat.card f.ker * Nat.card g.ker := by
  let g' : (f.comp g).ker →+ f.ker :=
    { toFun := fun x => ⟨g x, AddMonoidHom.mem_ker.mpr (AddMonoidHom.mem_ker.mp x.2)⟩
      map_zero' := by
        apply Subtype.ext
        simp
      map_add' := fun x y => by
        apply Subtype.ext
        simp }
  have h1 := AddSubgroup.card_ker_mul_card_range g'
  have h2 : Nat.card g'.range ≤ Nat.card f.ker :=
    Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  have h3 : Nat.card g'.ker ≤ Nat.card g.ker := by
    let ι : g'.ker → g.ker := fun x => ⟨x.1.1, by
      have hx := x.2
      rw [AddMonoidHom.mem_ker] at hx
      have := congrArg Subtype.val hx
      simpa [g'] using this⟩
    have hι : Function.Injective ι := by
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    exact Nat.card_le_card_of_injective ι hι
  calc Nat.card (f.comp g).ker = Nat.card g'.ker * Nat.card g'.range := h1.symm
    _ ≤ Nat.card g.ker * Nat.card f.ker := Nat.mul_le_mul h3 h2
    _ = Nat.card f.ker * Nat.card g.ker := Nat.mul_comm _ _

end KerComp

section Fixed

variable {V : Type*} [AddCommGroup V] [Finite V]

theorem card_le_card_ker_sub_pow_three (h3 : ∀ v : V, 3 • v = 0) (φ : V →+ V)
    (hφ : ∀ v, φ (φ (φ v)) = v) :
    Nat.card V ≤ Nat.card (φ - AddMonoidHom.id V).ker ^ 3 := by
  set N := φ - AddMonoidHom.id V with hN
  have hN3 : ∀ v, N (N (N v)) = 0 := by
    intro v
    simp only [hN, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, map_sub, hφ]
    have h := h3 (φ (φ v) - φ v)
    rw [smul_sub] at h
    have e : v - φ (φ v) - (φ (φ v) - φ v) - (φ (φ v) - φ v - (φ v - v)) =
        -(3 • φ (φ v) - 3 • φ v) := by abel
    rw [e, h, neg_zero]
  have htop : (N.comp (N.comp N)).ker = ⊤ := by
    ext v
    simp [hN3]
  have h1 := card_ker_comp_le N (N.comp N)
  have h2 := card_ker_comp_le N N
  rw [htop, AddSubgroup.card_top] at h1
  calc Nat.card V ≤ Nat.card N.ker * Nat.card (N.comp N).ker := h1
    _ ≤ Nat.card N.ker * (Nat.card N.ker * Nat.card N.ker) := Nat.mul_le_mul_left _ h2
    _ = Nat.card N.ker ^ 3 := by ring

end Fixed

section Special

variable {G : Type*} [Group G] [Finite G]

open Subgroup

theorem prime_mul_card_le_of_lt {p : ℕ} [hp : Fact p.Prime] {H K : Subgroup G}
    (hK : IsPGroup p K) (hHK : H < K) : p * Nat.card H ≤ Nat.card K := by
  obtain ⟨n, hn⟩ := hK.exists_card_eq
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK.le
  rw [hn] at hdvd
  obtain ⟨m, hm, hHm⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
  have hne : Nat.card H ≠ Nat.card K := fun h =>
    hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le h.symm.le)
  rw [hn] at hne ⊢
  rw [hHm] at hne ⊢
  have hlt : m < n := lt_of_le_of_ne hm fun h => hne (by rw [h])
  calc p * p ^ m = p ^ (m + 1) := by ring
    _ ≤ p ^ n := Nat.pow_le_pow_right hp.out.pos hlt

theorem eightyOne_dvd_card_inf_centralizer_of_special {Q S : Subgroup G} {k : ℕ} (hk : 4 ≤ k)
    (hQ : Nat.card Q = 3 ^ (2 * k + 1)) (hZ : Nat.card (center Q) = 3)
    (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ center Q) (hcube : ∀ x : Q, x ^ 3 ∈ center Q)
    (hQS : Q ≤ S) {s : G} (hsS : s ∈ S) (hs : s ∈ normalizer (Q : Set G)) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set G)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsQ : ∀ x : G, x ∈ Q ↔ s * x * s⁻¹ ∈ Q := fun x => mem_normalizer_iff.mp hs x
  have hsQ' : ∀ x : G, x ∈ Q → s⁻¹ * x * s ∈ Q := fun x hx => by
    have := (hsQ (s⁻¹ * x * s)).mpr
    apply this
    simpa [mul_assoc] using hx
  let φ : Q →* Q :=
    { toFun := fun x => ⟨s * x * s⁻¹, (hsQ x).mp x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp only [Subgroup.coe_mul]; group }
  have hφ_apply : ∀ x : Q, ((φ x : Q) : G) = s * x * s⁻¹ := fun _ => rfl
  have hφ_surj : ∀ y : Q, ∃ x : Q, φ x = y := fun y =>
    ⟨⟨s⁻¹ * y * s, hsQ' y y.2⟩, by ext; simp [hφ_apply, mul_assoc]⟩
  have hφ3 : ∀ x : Q, φ (φ (φ x)) = x := fun x => by
    ext
    simp only [hφ_apply]
    have e : s * (s * (s * (x : G) * s⁻¹) * s⁻¹) * s⁻¹ = (s * s * s) * x * (s * s * s)⁻¹ := by
      group
    have hsss : s * s * s = 1 := by rw [← hs3, pow_three, mul_assoc]
    rw [e, hsss]
    group
  have hφZ : center Q ≤ (center Q).comap φ := by
    intro z hz
    rw [mem_comap, mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := hφ_surj y
    rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) x]
  let _ : CommGroup (Q ⧸ center Q) :=
    { (inferInstance : Group (Q ⧸ center Q)) with
      mul_comm := by
        rintro ⟨a⟩ ⟨b⟩
        change ((a * b : Q) : Q ⧸ center Q) = ((b * a : Q) : Q ⧸ center Q)
        rw [QuotientGroup.eq]
        have h := hcomm b⁻¹ a⁻¹
        have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
        rw [e]
        exact h }
  let φbar : Q ⧸ center Q →* Q ⧸ center Q := QuotientGroup.map (center Q) (center Q) φ hφZ
  have hφbar3 : ∀ v, φbar (φbar (φbar v)) = v := by
    rintro ⟨x⟩
    change ((φ (φ (φ x)) : Q) : Q ⧸ center Q) = (x : Q ⧸ center Q)
    rw [hφ3]
  let V := Additive (Q ⧸ center Q)
  let φ' : V →+ V := MonoidHom.toAdditive φbar
  have h3 : ∀ v : V, 3 • v = 0 := by
    intro v
    change Additive.ofMul ((Additive.toMul v) ^ 3) = Additive.ofMul 1
    congr 1
    obtain ⟨x⟩ := Additive.toMul v
    change ((x ^ 3 : Q) : Q ⧸ center Q) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hcube x)
  have hφ'3 : ∀ v : V, φ' (φ' (φ' v)) = v := fun v => hφbar3 (Additive.toMul v)
  have hfix := card_le_card_ker_sub_pow_three h3 φ' hφ'3
  have hV : Nat.card V = 3 ^ (2 * k) := by
    have h1 := Subgroup.card_mul_index (center Q)
    rw [hZ, hQ] at h1
    change Nat.card (Q ⧸ center Q) = 3 ^ (2 * k)
    rw [← Subgroup.index]
    have : 3 ^ (2 * k + 1) = 3 * 3 ^ (2 * k) := by ring
    omega
  let Fix : Subgroup (Q ⧸ center Q) := MonoidHom.eqLocus φbar (MonoidHom.id _)
  have hmemFix : ∀ v, v ∈ Fix ↔ φbar v = v := fun v => Iff.rfl
  have hFixcard : Nat.card (φ' - AddMonoidHom.id V).ker = Nat.card Fix := by
    apply Nat.card_congr
    refine Equiv.subtypeEquiv Additive.toMul fun x => ?_
    rw [AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, AddMonoidHom.id_apply, sub_eq_zero]
    exact ⟨fun h => congrArg Additive.toMul h, fun h => congrArg Additive.ofMul h⟩
  rw [hFixcard, hV] at hfix
  have hVp : IsPGroup 3 (Q ⧸ center Q) := IsPGroup.of_card (by
    change Nat.card V = 3 ^ (2 * k)
    exact hV)
  obtain ⟨m, hm⟩ := (hVp.to_subgroup Fix).exists_card_eq
  have hm3 : 3 ≤ m := by
    rw [hm, ← pow_mul] at hfix
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hfix
    omega
  have hFix27 : 27 ≤ Nat.card Fix := by
    rw [hm]
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm3
  let P : Subgroup Q := Fix.comap (QuotientGroup.mk' (center Q))
  have hZP : center Q ≤ P := fun z hz => by
    show φbar (QuotientGroup.mk' (center Q) z) = QuotientGroup.mk' (center Q) z
    have h1 : QuotientGroup.mk' (center Q) z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [h1, map_one]
  have hcardP : Nat.card P = 3 * Nat.card Fix := by
    let r : P →* Fix := ((QuotientGroup.mk' (center Q)).comp P.subtype).codRestrict Fix
      fun x => x.2
    have hr : Function.Surjective r := by
      rintro ⟨v, hv⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center Q) v
      exact ⟨⟨x, hv⟩, rfl⟩
    have h1 := Subgroup.card_ker_mul_card_of_surjective hr
    have hker : Nat.card r.ker = Nat.card (center Q) := by
      have hmem : ∀ x : P, x ∈ r.ker ↔ (x : Q) ∈ center Q := fun x => by
        rw [MonoidHom.mem_ker]
        constructor
        · intro hx
          have := congrArg Subtype.val hx
          exact (QuotientGroup.eq_one_iff _).mp this
        · intro hx
          apply Subtype.ext
          exact (QuotientGroup.eq_one_iff _).mpr hx
      let e : r.ker ≃ center Q :=
        { toFun := fun x => ⟨x.1.1, (hmem x.1).mp x.2⟩
          invFun := fun z => ⟨⟨z.1, hZP z.2⟩, (hmem _).mpr z.2⟩
          left_inv := fun x => rfl
          right_inv := fun z => rfl }
      exact Nat.card_congr e
    rw [← h1, hker, hZ]
  have hcP : ∀ x : Q, x ∈ P → φ x * x⁻¹ ∈ center Q := by
    intro x hx
    have h1 : (QuotientGroup.mk' (center Q) (φ x)) = QuotientGroup.mk' (center Q) x := hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
    have hnorm : (center Q).Normal := inferInstance
    have h2 : x * ((φ x)⁻¹ * x)⁻¹ * x⁻¹ ∈ center Q :=
      hnorm.conj_mem _ ((center Q).inv_mem h1) x
    have e : x * ((φ x)⁻¹ * x)⁻¹ * x⁻¹ = φ x * x⁻¹ := by group
    rwa [e] at h2
  let c : P →* center Q :=
    { toFun := fun x => ⟨φ x * (x : Q)⁻¹, hcP x x.2⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        apply Subtype.ext
        have hy := mem_center_iff.mp (hcP y y.2) (x : Q)⁻¹
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc φ x * φ y * ((y : Q)⁻¹ * (x : Q)⁻¹) = φ x * (φ y * (y : Q)⁻¹ * (x : Q)⁻¹) := by group
          _ = φ x * ((x : Q)⁻¹ * (φ y * (y : Q)⁻¹)) := by rw [hy]
          _ = φ x * (x : Q)⁻¹ * (φ y * (y : Q)⁻¹) := by group }
  have hkerc : Nat.card Fix ≤ Nat.card c.ker := by
    have h1 := Subgroup.card_ker_mul_card_range c
    have h2 : Nat.card c.range ≤ 3 := by
      rw [← hZ]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    rw [hcardP] at h1
    nlinarith
  let C' : Subgroup G := Q ⊓ centralizer ({s} : Set G)
  have hC'Q : C' ≤ Q := inf_le_left
  have hC'p : IsPGroup 3 C' := by
    have hQp : IsPGroup 3 Q := IsPGroup.of_card hQ
    exact hQp.to_le hC'Q
  have hcardC' : Nat.card Fix ≤ Nat.card C' := by
    refine hkerc.trans (Nat.card_le_card_of_injective (fun x => ⟨x.1.1.1, x.1.1.2, ?_⟩) ?_)
    · show (x.1.1 : G) ∈ centralizer ({s} : Set G)
      rw [mem_centralizer_singleton_iff]
      have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      have h1 := congrArg (fun y : center Q => ((y : Q) : G)) hx
      simp only [c, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv,
        OneMemClass.coe_one, hφ_apply] at h1
      have h2 : s * (x.1.1 : G) = (x.1.1 : G) * s := by
        rw [mul_inv_eq_one] at h1
        calc s * (x.1.1 : G) = s * (x.1.1 : G) * s⁻¹ * s := by group
          _ = (x.1.1 : G) * s := by rw [h1]
      exact h2.symm
    · intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext (Subtype.ext h))
  have h81 : ∀ H : Subgroup G, IsPGroup 3 H → 81 ≤ Nat.card H →
      H ≤ S ⊓ centralizer ({s} : Set G) → 81 ∣ Nat.card ↥(S ⊓ centralizer ({s} : Set G)) := by
    intro H hH h81 hHC
    obtain ⟨n, hn⟩ := hH.exists_card_eq
    have hn4 : 4 ≤ n := by
      by_contra hlt
      push Not at hlt
      have : 3 ^ n ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hn] at h81
      norm_num at this
      omega
    have hdvd : 81 ∣ Nat.card H := by
      rw [hn]
      exact (show 81 = 3 ^ 4 by norm_num) ▸ Nat.pow_dvd_pow 3 hn4
    exact hdvd.trans (Subgroup.card_dvd_of_le hHC)
  by_cases hsQin : s ∈ Q
  ·
    have hFixtop : ∀ v, v ∈ Fix := by
      rintro ⟨x⟩
      show φbar (x : Q ⧸ center Q) = x
      change ((φ x : Q) : Q ⧸ center Q) = (x : Q ⧸ center Q)
      have e : φ x = ⟨s, hsQin⟩ * x * ⟨s, hsQin⟩⁻¹ := by
        ext
        simp [hφ_apply]
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul, mul_comm (((⟨s, hsQin⟩ : Q)) : Q ⧸ center Q),
        mul_assoc, ← QuotientGroup.mk_mul, mul_inv_cancel, QuotientGroup.mk_one, mul_one]
    have hFixV : Nat.card Fix = 3 ^ (2 * k) := by
      have : Fix = ⊤ := eq_top_iff.mpr fun v _ => hFixtop v
      rw [this, Subgroup.card_top]
      exact hV
    refine h81 C' hC'p ?_ (le_inf (hC'Q.trans hQS) inf_le_right)
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ 3 ^ (2 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = Nat.card Fix := hFixV.symm
      _ ≤ Nat.card C' := hcardC'
  ·
    have hsp : IsPGroup 3 (zpowers s) := by
      apply IsPGroup.of_card (n := if s = 1 then 0 else 1)
      rw [Nat.card_zpowers]
      split_ifs with h1
      · rw [h1, orderOf_one, pow_zero]
      · rw [pow_one]
        exact orderOf_eq_prime hs3 h1
    have hsN : zpowers s ≤ normalizer (C' : Set G) := by
      rw [zpowers_le]
      rw [mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxs : x * s = s * x := mem_centralizer_singleton_iff.mp hx.2
        have e : s * x * s⁻¹ = x := by rw [← hxs]; group
        rw [e]
        exact hx
      · intro hx
        have hxs : s * x * s⁻¹ * s = s * (s * x * s⁻¹) := mem_centralizer_singleton_iff.mp hx.2
        have e : s * x * s⁻¹ = x := by
          have : s * x * s⁻¹ * s = s * x := by group
          rw [this] at hxs
          exact (mul_left_cancel hxs).symm
        rw [e] at hx
        exact hx
    set H : Subgroup G := zpowers s ⊔ C' with hHdef
    have hHp : IsPGroup 3 H := IsPGroup.to_sup_of_normal_right' hsp hC'p hsN
    have hlt : C' < H := by
      refine lt_of_le_of_ne le_sup_right fun h => hsQin ?_
      have : s ∈ H := (le_sup_left : zpowers s ≤ H) (mem_zpowers s)
      rw [← h] at this
      exact this.1
    have hle : 3 * Nat.card C' ≤ Nat.card H := prime_mul_card_le_of_lt hHp hlt
    refine h81 H hHp (le_trans (by omega : 81 ≤ 3 * Nat.card C') hle) (le_inf ?_ ?_)
    · exact sup_le ((zpowers_le (H := S)).mpr hsS) (hC'Q.trans hQS)
    · refine sup_le ?_ (inf_le_right : C' ≤ centralizer ({s} : Set G))
      rw [zpowers_le]
      exact mem_centralizer_singleton_iff.mpr rfl

theorem eightyOne_dvd_card_centralizer_of_special {Q : Subgroup G} {k : ℕ} (hk : 4 ≤ k)
    (hQ : Nat.card Q = 3 ^ (2 * k + 1)) (hZ : Nat.card (center Q) = 3)
    (hcomm : ∀ x y : Q, x * y * x⁻¹ * y⁻¹ ∈ center Q) (hcube : ∀ x : Q, x ^ 3 ∈ center Q)
    {s : G} (hs : s ∈ normalizer (Q : Set G)) (hs3 : s ^ 3 = 1) :
    81 ∣ Nat.card (centralizer ({s} : Set G)) := by
  have h := eightyOne_dvd_card_inf_centralizer_of_special hk hQ hZ hcomm hcube le_top
    (mem_top s) hs hs3
  rwa [top_inf_eq] at h

end Special

end CFSG.HardMathSupport.Foote.E27
