module

public import CFSG.CGT.Stroth77.Arch76Lemma2
public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.CGT.Stroth77.Arch76

namespace Config

section Restrict

variable {G : Type*} [Group G] (C : Config G) (N : Subgroup G)

@[expose] def restrict (hA : C.A ≤ N) (huv : C.uv ∈ N) (ht : C.t ∈ N) (hu : C.u ∈ N)
    (hρ : C.ρ ∈ N) : Config N where
  A := C.A.subgroupOf N
  w := ⟨C.w, hA C.w_mem⟩
  x := ⟨C.x, hA C.x_mem⟩
  y := ⟨C.y, hA C.y_mem⟩
  uv := ⟨C.uv, huv⟩
  t := ⟨C.t, ht⟩
  u := ⟨C.u, hu⟩
  ρ := ⟨C.ρ, hρ⟩
  hA := by
    apply le_antisymm
    · intro z hz
      obtain ⟨v, hv⟩ := C.exists_ev (Subgroup.mem_subgroupOf.mp hz)
      have hz' : z = (⟨C.w, hA C.w_mem⟩ : N) ^ v.1.val * (⟨C.x, hA C.x_mem⟩ : N) ^ v.2.1.val *
          (⟨C.y, hA C.y_mem⟩ : N) ^ v.2.2.val := Subtype.ext (by simp [← hv, ev])
      rw [hz']
      exact mul_mem (mul_mem (pow_mem (Subgroup.subset_closure (by simp)) _)
        (pow_mem (Subgroup.subset_closure (by simp)) _))
        (pow_mem (Subgroup.subset_closure (by simp)) _)
    · rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      exacts [Subgroup.mem_subgroupOf.mpr C.w_mem, Subgroup.mem_subgroupOf.mpr C.x_mem,
        Subgroup.mem_subgroupOf.mpr C.y_mem]
  hAc := ⟨⟨fun a b => Subtype.ext (Subtype.ext
    (C.comm (Subgroup.mem_subgroupOf.mp a.2) (Subgroup.mem_subgroupOf.mp b.2)))⟩⟩
  hAcard := by rw [← C.hAcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv
  hw := Subtype.ext (by simpa using C.hw)
  hx := Subtype.ext (by simpa using C.hx)
  hy := Subtype.ext (by simpa using C.hy)
  huv_w := Subtype.ext (by simpa using C.huv_w)
  huv_x := Subtype.ext (by simpa using C.huv_x)
  huv_y := Subtype.ext (by simpa using C.huv_y)
  ht_w := Subtype.ext (by simpa using C.ht_w)
  ht_x := Subtype.ext (by simpa using C.ht_x)
  ht_y := Subtype.ext (by simpa using C.ht_y)
  hu_w := Subtype.ext (by simpa using C.hu_w)
  hu_x := Subtype.ext (by simpa using C.hu_x)
  hρ_w := Subtype.ext (by simpa using C.hρ_w)
  hρ_x := Subtype.ext (by simpa using C.hρ_x)
  hρ_y := Subtype.ext (by simpa using C.hρ_y)
  huv2 := Subtype.ext (by simpa using C.huv2)
  ht2 := Subtype.ext (by simpa using C.ht2)
  hu2 := Subtype.ext (by simpa using C.hu2)
  huvt := Subtype.ext (by simpa using C.huvt)
  huvu := Subtype.ext (by simpa using C.huvu)
  htu := Subtype.ext (by simpa using C.htu)
  hρuv := Subtype.ext (by simpa using C.hρuv)
  hρt := Subtype.ext (by simpa using C.hρt)
  hρu := Subtype.ext (by simpa using C.hρu)

end Restrict

section Map

variable {G H : Type*} [Group G] [Group H] (C : Config G) (f : G →* H)

@[expose] def map (hf : Set.InjOn f C.A) : Config H where
  A := C.A.map f
  w := f C.w
  x := f C.x
  y := f C.y
  uv := f C.uv
  t := f C.t
  u := f C.u
  ρ := f C.ρ
  hA := by
    rw [C.hA, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
  hAc := ⟨⟨fun a b => by
    obtain ⟨a', ha', ha⟩ := Subgroup.mem_map.mp a.2
    obtain ⟨b', hb', hb⟩ := Subgroup.mem_map.mp b.2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← ha, ← hb, ← map_mul, C.comm ha' hb']⟩⟩
  hAcard := by
    rw [← C.hAcard]
    exact Nat.card_image_of_injOn hf
  hw := by rw [← map_pow, C.hw, map_one]
  hx := by rw [← map_pow, C.hx, map_one]
  hy := by rw [← map_pow, C.hy, map_one]
  huv_w := by simpa using congrArg f C.huv_w
  huv_x := by simpa using congrArg f C.huv_x
  huv_y := by simpa using congrArg f C.huv_y
  ht_w := by simpa using congrArg f C.ht_w
  ht_x := by simpa using congrArg f C.ht_x
  ht_y := by simpa using congrArg f C.ht_y
  hu_w := by simpa using congrArg f C.hu_w
  hu_x := by simpa using congrArg f C.hu_x
  hρ_w := by simpa using congrArg f C.hρ_w
  hρ_x := by simpa using congrArg f C.hρ_x
  hρ_y := by simpa using congrArg f C.hρ_y
  huv2 := by rw [← map_pow, C.huv2, map_one]
  ht2 := by rw [← map_pow, C.ht2, map_one]
  hu2 := by rw [← map_pow, C.hu2, map_one]
  huvt := by simpa using congrArg f C.huvt
  huvu := by simpa using congrArg f C.huvu
  htu := by simpa using congrArg f C.htu
  hρuv := by simpa using congrArg f C.hρuv
  hρt := by simpa using congrArg f C.hρt
  hρu := by simpa using congrArg f C.hρu

end Map

end Config

section Odd

variable {Y : Type*} [Group Y]

theorem eq_one_of_mem_of_odd {O : Subgroup Y} (hO : ¬ 2 ∣ Nat.card O) {x : Y} (hx : x ∈ O)
    (h2 : ∃ n : ℕ, x ^ 2 ^ n = 1) : x = 1 := by
  obtain ⟨n, hn⟩ := h2
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn)
  have hd := O.orderOf_dvd_natCard hx
  rw [hj] at hd
  rcases j with _ | j
  · exact orderOf_eq_one_iff.mp (by simpa using hj)
  · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero j)) hd) hO

theorem injOn_of_isPGroup {O : Subgroup Y} [O.Normal] (hO : ¬ 2 ∣ Nat.card O) {P : Subgroup Y}
    (hP : IsPGroup 2 P) : Set.InjOn (QuotientGroup.mk' O) P := by
  intro a ha b hb h
  have hab : a⁻¹ * b ∈ O := QuotientGroup.eq.mp h
  obtain ⟨n, hn⟩ := hP ⟨a⁻¹ * b, mul_mem (inv_mem ha) hb⟩
  have h1 := eq_one_of_mem_of_odd hO hab ⟨n, by simpa using congrArg Subtype.val hn⟩
  exact inv_mul_eq_one.mp h1

theorem le_of_map_le {O : Subgroup Y} [O.Normal] (hO : ¬ 2 ∣ Nat.card O) {P R : Subgroup Y}
    (hP : IsPGroup 2 P) (hRP : R ≤ P)
    (h : P.map (QuotientGroup.mk' O) ≤ R.map (QuotientGroup.mk' O)) : P ≤ R := by
  intro p hp
  obtain ⟨r, hr, hrp⟩ := Subgroup.mem_map.mp (h (Subgroup.mem_map_of_mem _ hp))
  rw [← injOn_of_isPGroup hO hP (hRP hr) hp hrp]
  exact hr

theorem mem_normalizer_of_map {O : Subgroup Y} [O.Normal] (hO : ¬ 2 ∣ Nat.card O)
    {P E : Subgroup Y} (hP : IsPGroup 2 P) (hEP : E ≤ P) {g : Y} (hg : g ∈ P)
    (hgE : QuotientGroup.mk' O g ∈
      Subgroup.normalizer ((E.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))) :
    g ∈ Subgroup.normalizer (E : Set Y) := by
  set π := QuotientGroup.mk' O
  have hinj := injOn_of_isPGroup hO hP
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have hmem : g * h * g⁻¹ ∈ P := mul_mem (mul_mem hg (hEP hh)) (inv_mem hg)
    have h1 := (Subgroup.mem_normalizer_iff.mp hgE (π h)).mp (Subgroup.mem_map_of_mem π hh)
    rw [← map_inv, ← map_mul, ← map_mul] at h1
    obtain ⟨e, he, hπe⟩ := Subgroup.mem_map.mp h1
    rw [← hinj (hEP he) hmem hπe]
    exact he
  · intro hh
    have hmem : h ∈ P := by
      have := mul_mem (mul_mem (inv_mem hg) (hEP hh)) hg
      rwa [show g⁻¹ * (g * h * g⁻¹) * g = h by group] at this
    have h1 := (Subgroup.mem_normalizer_iff.mp hgE (π h)).mpr (by
      rw [← map_inv, ← map_mul, ← map_mul]; exact Subgroup.mem_map_of_mem π hh)
    obtain ⟨e, he, hπe⟩ := Subgroup.mem_map.mp h1
    rw [← hinj (hEP he) hmem hπe]
    exact he

theorem centralizer_map_mk' {A O Q : Subgroup Y} [A.Normal] [O.Normal] (hA2 : IsPGroup 2 A)
    (hO : ¬ 2 ∣ Nat.card O) (hQC : Q ≤ Subgroup.centralizer (A : Set Y))
    (hZ : Subgroup.centralizer (A : Set Y) ≤ Q ⊔ O) :
    Subgroup.centralizer ((A.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O)) =
      Q.map (QuotientGroup.mk' O) := by
  set π := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  apply le_antisymm
  · intro z hz
    obtain ⟨y, rfl⟩ := hπs z
    have hyZ : y ∈ Subgroup.centralizer (A : Set Y) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h1 := Subgroup.mem_centralizer_iff.mp hz (π a) (Subgroup.mem_map_of_mem π ha)
      have h2 : a * y * a⁻¹ * y⁻¹ ∈ O := by
        apply (QuotientGroup.eq_one_iff (a * y * a⁻¹ * y⁻¹)).mp
        change π (a * y * a⁻¹ * y⁻¹) = 1
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, h1]; group
      have h3 : a * y * a⁻¹ * y⁻¹ ∈ A := by
        have := (inferInstance : A.Normal).conj_mem a⁻¹ (inv_mem ha) y
        rw [show a * y * a⁻¹ * y⁻¹ = a * (y * a⁻¹ * y⁻¹) by group]
        exact mul_mem ha this
      have h4 := eq_one_of_mem_of_odd hO h2 (by
        obtain ⟨n, hn⟩ := hA2 ⟨_, h3⟩
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩)
      calc a * y = a * y * a⁻¹ * y⁻¹ * (y * a) := by group
        _ = y * a := by rw [h4, one_mul]
    have hmem : y ∈ ((Q ⊔ O : Subgroup Y) : Set Y) := hZ hyZ
    rw [Subgroup.mul_normal, Set.mem_mul] at hmem
    obtain ⟨q, hq, k, hk, rfl⟩ := hmem
    rw [map_mul, show π k = 1 from (QuotientGroup.eq_one_iff k).mpr hk, mul_one]
    exact Subgroup.mem_map_of_mem π hq
  · rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_centralizer_iff.mp (hQC hq)) a ha]

theorem exists_oddComplement [Finite Y] (A : Subgroup Y) [A.Normal] (hAc : IsMulCommutative A)
    (hA2 : IsPGroup 2 A) (hAZ : ¬ 2 ∣ A.relIndex (Subgroup.centralizer (A : Set Y))) :
    ∃ O : Subgroup Y, O.Normal ∧ O ≤ Subgroup.centralizer (A : Set Y) ∧ ¬ 2 ∣ Nat.card O ∧
      Subgroup.centralizer (A : Set Y) ≤ A ⊔ O := by
  set Z := Subgroup.centralizer (A : Set Y) with hZ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Z.Normal := Subgroup.normal_centralizer
  have hAZle : A ≤ Z := fun a ha => Subgroup.mem_centralizer_iff.mpr fun b hb =>
    Subgroup.mul_comm_of_mem_isMulCommutative A hb ha
  have hP2 : IsPGroup 2 (A.subgroupOf Z) := hA2.comap_of_injective Z.subtype Subtype.val_injective
  let Psyl : Sylow 2 Z := hP2.toSylow hAZ
  have hcen : Subgroup.normalizer (Psyl : Set Z) ≤ Subgroup.centralizer (Psyl : Set Z) := by
    intro z _
    rw [Subgroup.mem_centralizer_iff]
    intro p hp
    exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp z.2) p (Subgroup.mem_subgroupOf.mp hp))
  haveI : (Psyl : Subgroup Z).FiniteIndex := inferInstance
  set K := (MonoidHom.transferSylow Psyl hcen).ker
  have hK := MonoidHom.ker_transferSylow_isComplement' Psyl hcen
  have hKodd := MonoidHom.not_dvd_card_ker_transferSylow Psyl hcen
  set O := K.map Z.subtype with hO
  have hOcard : Nat.card O = Nat.card K := Nat.card_congr
    (Subgroup.equivMapOfInjective K Z.subtype Subtype.val_injective).toEquiv.symm
  have hOZ : O ≤ Z := by rw [hO]; exact Subgroup.map_subtype_le K
  have hOodd : ¬ 2 ∣ Nat.card O := by rw [hOcard]; exact hKodd
  have hAO : ∀ a ∈ A, a ∈ O → a = 1 := fun a ha hao =>
    eq_one_of_mem_of_odd hOodd hao (by
      obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩)
  have hZAO : Z ≤ A ⊔ O := by
    intro z hz
    have h1 : (⟨z, hz⟩ : Z) ∈ K ⊔ (Psyl : Subgroup Z) := by rw [hK.sup_eq_top]; trivial
    have h2 := Subgroup.mem_map_of_mem Z.subtype h1
    have hPs : (Psyl : Subgroup Z) = A.subgroupOf Z := rfl
    rw [Subgroup.map_sup, ← hO, hPs, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hAZle, sup_comm] at h2
    exact h2
  refine ⟨O, ⟨fun o ho y => ?_⟩, hOZ, hOodd, hZAO⟩
  set o' := y * o * y⁻¹
  have ho'Z : o' ∈ Z := (inferInstance : Z.Normal).conj_mem o (hOZ ho) y
  have hord : ¬ 2 ∣ orderOf o' := by
    rw [show orderOf o' = orderOf o from
      orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective o]
    exact fun h => hOodd (h.trans (O.orderOf_dvd_natCard ho))
  have hmem : o' ∈ ((A ⊔ O : Subgroup Y) : Set Y) := hZAO ho'Z
  rw [Subgroup.normal_mul, Set.mem_mul] at hmem
  obtain ⟨a, ha, k, hk, hak⟩ := hmem
  have hcomm : Commute a k := Subgroup.mem_centralizer_iff.mp (hOZ hk) a ha
  have hpow : a ^ orderOf o' * k ^ orderOf o' = 1 := by
    rw [← hcomm.mul_pow, hak, pow_orderOf_eq_one]
  have ha1 : a ^ orderOf o' = 1 := by
    have h3 : a ^ orderOf o' = (k ^ orderOf o')⁻¹ := eq_inv_of_mul_eq_one_left hpow
    exact hAO _ (pow_mem ha _) (by rw [h3]; exact inv_mem (pow_mem hk _))
  have ha' : a = 1 := by
    obtain ⟨n, hn⟩ := hA2 ⟨a, ha⟩
    have hn' : a ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hn')
    have hd := orderOf_dvd_of_pow_eq_one ha1
    rw [hj] at hd
    rcases j with _ | j
    · exact orderOf_eq_one_iff.mp (by simpa using hj)
    · exact absurd (dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero j)) hd) hord
  rw [← hak, ha', one_mul]
  exact hk

end Odd

namespace Config

variable {Y : Type*} [Group Y] [Finite Y] (C : Config Y)

theorem isPGroup_A : IsPGroup 2 C.A := fun a => ⟨2, by
  obtain ⟨v, hv⟩ := C.exists_ev a.2
  apply Subtype.ext
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hv, ← ev_nsmul, show 2 ^ 2 = 4 by norm_num,
    four_nsmul_eq, ev_zero]⟩

theorem A_le_centralizer : C.A ≤ Subgroup.centralizer (C.A : Set Y) := fun a ha =>
  Subgroup.mem_centralizer_iff.mpr fun b hb => C.comm hb ha

theorem not_dvd_relIndex_centralizer [C.A.Normal] (P : Sylow 2 Y)
    (hCP : Subgroup.centralizer (C.A : Set Y) ⊓ P = C.A) :
    ¬ 2 ∣ C.A.relIndex (Subgroup.centralizer (C.A : Set Y)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Z := Subgroup.centralizer (C.A : Set Y)
  haveI : Z.Normal := Subgroup.normal_centralizer
  have h1 := Subgroup.relIndex_mul_relIndex ((P : Subgroup Y) ⊓ Z) P ((P : Subgroup Y) ⊔ Z)
    inf_le_left le_sup_left
  have h2 := Subgroup.relIndex_mul_relIndex ((P : Subgroup Y) ⊓ Z) Z ((P : Subgroup Y) ⊔ Z)
    inf_le_right le_sup_right
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.relIndex_sup_right] at h2
  have hne : Z.relIndex (P : Subgroup Y) ≠ 0 :=
    (Subgroup.isFiniteRelIndex_iff_finiteIndex.mpr inferInstance).relIndex_ne_zero
  have key : ((P : Subgroup Y) ⊓ Z).relIndex Z = (P : Subgroup Y).relIndex ((P : Subgroup Y) ⊔ Z) :=
    (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hne) (by rw [h1, ← h2, mul_comm])).symm
  rw [show C.A = (P : Subgroup Y) ⊓ Z by rw [inf_comm, hCP], key]
  exact fun h => P.not_dvd_index (h.trans (Subgroup.relIndex_dvd_index_of_le le_sup_left))

theorem lemma2_of_centralizer_inf [C.A.Normal] (hρodd : Odd (orderOf C.ρ)) (P : Sylow 2 Y)
    (hTP : C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} ≤ P)
    (hE : ∀ g ∈ (P : Subgroup Y),
      g ∈ Subgroup.normalizer (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} : Set Y) →
        g ∈ C.A ⊔ Subgroup.closure {C.uv, C.t, C.u})
    (hCP : Subgroup.centralizer (C.A : Set Y) ⊓ P = C.A) :
    (P : Subgroup Y) = C.A ⊔ Subgroup.closure {C.uv, C.t, C.u} ∨
      ∃ s ∈ (P : Subgroup Y), (P : Subgroup Y) = C.A ⊔ Subgroup.closure {C.uv, C.t, C.u, s} ∧
        s ^ 2 = 1 ∧ s⁻¹ * C.w * s = C.w ∧ s⁻¹ * C.x * s = C.x⁻¹ ∧ s⁻¹ * C.y * s = C.y⁻¹ ∧
        ((s⁻¹ * C.uv * s = C.x * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.t ∧
            s⁻¹ * C.u * s = C.u) ∨
          (s⁻¹ * C.uv * s = C.x⁻¹ * C.y * C.uv ∧ s⁻¹ * C.t * s = C.x⁻¹ * C.y ^ 2 * C.t ∧
            s⁻¹ * C.u * s = C.w * C.u)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨O, hON, hOZ, hOodd, hZAO⟩ := exists_oddComplement C.A C.hAc C.isPGroup_A
    (C.not_dvd_relIndex_centralizer P hCP)
  haveI := hON
  set π := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hP2 : IsPGroup 2 (P : Subgroup Y) := P.isPGroup'
  have hinjP := injOn_of_isPGroup hOodd hP2
  have hAP : C.A ≤ P := le_sup_left.trans hTP
  have hinjA : Set.InjOn π C.A := hinjP.mono hAP
  set CX := C.map π hinjA with hCX
  haveI : CX.A.Normal := (inferInstance : C.A.Normal).map π hπs
  have hρoddX : Odd (orderOf CX.ρ) := hρodd.of_dvd_nat (orderOf_map_dvd π C.ρ)
  have hCAX : Subgroup.centralizer (CX.A : Set (Y ⧸ O)) = CX.A :=
    centralizer_map_mk' C.isPGroup_A hOodd C.A_le_centralizer hZAO
  set PX := P.mapSurjective hπs with hPX
  have hPXc : (PX : Subgroup (Y ⧸ O)) = (P : Subgroup Y).map π := rfl
  have hTmap : (C.A ⊔ Subgroup.closure {C.uv, C.t, C.u}).map π =
      CX.A ⊔ Subgroup.closure {CX.uv, CX.t, CX.u} := by
    rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
    rfl
  have hEmap : (Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t}).map π =
      Subgroup.closure {CX.x ^ 2, CX.y ^ 2, CX.uv, CX.t} := by
    rw [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton, map_pow, map_pow]
    rfl
  have hTPX : CX.A ⊔ Subgroup.closure {CX.uv, CX.t, CX.u} ≤ PX := by
    rw [hPXc, ← hTmap]; exact Subgroup.map_mono hTP
  have hEP : Subgroup.closure {C.x ^ 2, C.y ^ 2, C.uv, C.t} ≤ (P : Subgroup Y) := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact hAP (pow_mem C.x_mem 2)
    · exact hAP (pow_mem C.y_mem 2)
    · exact hTP C.uv_mem_T
    · exact hTP C.t_mem_T
  have hEX : ∀ g ∈ (PX : Subgroup (Y ⧸ O)),
      g ∈ Subgroup.normalizer (Subgroup.closure {CX.x ^ 2, CX.y ^ 2, CX.uv, CX.t} :
        Set (Y ⧸ O)) → g ∈ CX.A ⊔ Subgroup.closure {CX.uv, CX.t, CX.u} := by
    intro g hg hgN
    rw [hPXc] at hg
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.mp hg
    rw [← hEmap] at hgN
    have := hE g' hg' (mem_normalizer_of_map hOodd hP2 hEP hg' hgN)
    rw [← hTmap]
    exact Subgroup.mem_map_of_mem π this
  have hlift : ∀ {a b : Y}, a ∈ (P : Subgroup Y) → b ∈ (P : Subgroup Y) → π a = π b → a = b :=
    fun ha hb h => hinjP ha hb h
  rcases CX.lemma2 hρoddX hCAX PX hTPX hEX with h | ⟨sX, hsX, hPeq, hs2, hsw, hsx, hsy, hrel⟩
  · left
    apply le_antisymm _ hTP
    apply le_of_map_le hOodd hP2 hTP
    rw [← hPXc, h, hTmap]
  · right
    rw [hPXc] at hsX
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hsX
    have hwP := hAP C.w_mem
    have hxP := hAP C.x_mem
    have hyP := hAP C.y_mem
    have huvP := hTP C.uv_mem_T
    have htP := hTP C.t_mem_T
    have huP := hTP C.u_mem_T
    have hcP : ∀ {g : Y}, g ∈ (P : Subgroup Y) → s⁻¹ * g * s ∈ (P : Subgroup Y) := fun hg =>
      mul_mem (mul_mem (inv_mem hs) hg) hs
    have hR : C.A ⊔ Subgroup.closure {C.uv, C.t, C.u, s} ≤ P := by
      refine sup_le hAP ?_
      rw [Subgroup.closure_le]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      exacts [huvP, htP, huP, hs]
    have hRmap : (C.A ⊔ Subgroup.closure {C.uv, C.t, C.u, s}).map π =
        CX.A ⊔ Subgroup.closure {CX.uv, CX.t, CX.u, π s} := by
      rw [Subgroup.map_sup, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_insert_eq, Set.image_singleton]
      rfl
    refine ⟨s, hs, le_antisymm (le_of_map_le hOodd hP2 hR (by rw [← hPXc, hPeq, hRmap])) hR,
      ?_, ?_, ?_, ?_, ?_⟩
    · exact hlift (pow_mem hs 2) (one_mem _) (by rw [map_pow, map_one]; exact hs2)
    · exact hlift (hcP hwP) hwP (by simp only [map_mul, map_inv, map_pow]; exact hsw)
    · exact hlift (hcP hxP) (inv_mem hxP) (by simp only [map_mul, map_inv, map_pow]; exact hsx)
    · exact hlift (hcP hyP) (inv_mem hyP) (by simp only [map_mul, map_inv, map_pow]; exact hsy)
    · rcases hrel with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
      · left
        exact ⟨hlift (hcP huvP) (mul_mem (mul_mem hxP hyP) huvP)
            (by simp only [map_mul, map_inv, map_pow]; exact h1),
          hlift (hcP htP) (mul_mem (inv_mem hxP) htP)
            (by simp only [map_mul, map_inv, map_pow]; exact h2),
          hlift (hcP huP) huP (by simp only [map_mul, map_inv, map_pow]; exact h3)⟩
      · right
        exact ⟨hlift (hcP huvP) (mul_mem (mul_mem (inv_mem hxP) hyP) huvP)
            (by simp only [map_mul, map_inv, map_pow]; exact h1),
          hlift (hcP htP) (mul_mem (mul_mem (inv_mem hxP) (pow_mem hyP 2)) htP)
            (by simp only [map_mul, map_inv, map_pow]; exact h2),
          hlift (hcP huP) (mul_mem hwP huP) (by simp only [map_mul, map_inv, map_pow]; exact h3)⟩

end Config

end CFSG.CGT.Stroth77.Arch76
