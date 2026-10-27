module

public import CFSG.GH74.GLS.C3.Layer2.L4End
public import CFSG.GH74.GLS.C3.Layer1.Th2P43fKRule
public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.CharacterTheory.Burnside

public section

namespace CFSG.GH74.GLS.Th2.P412

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer2.L4 CFSG.GH74.GLS.Th2.P43f
  CFSG.GH74.Uniqueness

section Basic

variable {C : Type} [Group C] [Finite C]

theorem odd_card_pPrimeCore : Odd (Nat.card (pPrimeCore 2 C)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Nat.coprime_two_left.1 pPrimeCore_coprime_card

theorem odd_orderOf_of_mem_pPrimeCore {o : C} (ho : o ∈ pPrimeCore 2 C) : Odd (orderOf o) :=
  Odd.of_dvd_nat odd_card_pPrimeCore (Subgroup.orderOf_dvd_natCard _ ho)

theorem eq_one_of_mem_pPrimeCore_of_sq {o : C} (ho : o ∈ pPrimeCore 2 C) (h : o * o = 1) :
    o = 1 := by
  have h2 : orderOf o ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact h)
  have hodd := odd_orderOf_of_mem_pPrimeCore ho
  have h1 : orderOf o = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h' | h'
    · exact h'
    · rw [h'] at hodd
      exact absurd hodd (by decide)
  exact orderOf_eq_one_iff.1 h1

theorem inf_pPrimeCore_eq_bot {S : Subgroup C} (hS : IsPGroup 2 ↥S) : S ⊓ pPrimeCore 2 C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine eq_bot_iff.2 fun g hg => ?_
  obtain ⟨hgS, hgO⟩ := hg
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hS) ⟨g, hgS⟩
  have h1 : orderOf g = 2 ^ k := by rwa [Subgroup.orderOf_mk] at hk
  have h2 : Odd (orderOf g) := odd_orderOf_of_mem_pPrimeCore hgO
  have hk0 : k = 0 := by
    by_contra hk0
    exact (Nat.not_even_iff_odd.2 h2) (h1 ▸ Nat.even_pow.2 ⟨even_two, hk0⟩)
  rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
  exact h1

theorem mk_injOn {S : Subgroup C} (hS : IsPGroup 2 ↥S) {s s' : C} (hs : s ∈ S) (hs' : s' ∈ S)
    (h : (QuotientGroup.mk' (pPrimeCore 2 C)) s = (QuotientGroup.mk' (pPrimeCore 2 C)) s') :
    s = s' := by
  have h1 : s⁻¹ * s' ∈ pPrimeCore 2 C := QuotientGroup.eq.1 h
  have h2 : s⁻¹ * s' ∈ S ⊓ pPrimeCore 2 C := ⟨S.mul_mem (S.inv_mem hs) hs', h1⟩
  rw [inf_pPrimeCore_eq_bot hS, Subgroup.mem_bot] at h2
  exact (inv_mul_eq_one.1 h2)

theorem exists_conj_of_inv_mul_mem {c c' : C} (hc : c * c = 1) (hc' : c' * c' = 1)
    (h : c⁻¹ * c' ∈ pPrimeCore 2 C) : ∃ w ∈ pPrimeCore 2 C, w * c * w⁻¹ = c' := by
  have hN := (pPrimeCore_normal (G := C) (p := 2))
  have hy : c * (c⁻¹ * c') * c⁻¹ ∈ pPrimeCore 2 C := hN.conj_mem _ h c
  have e : c * (c⁻¹ * c') * c⁻¹ = c' * c⁻¹ := by group
  rw [e] at hy
  have hc'c : c' = (c' * c⁻¹) * c := by group
  have hyc : ((c' * c⁻¹) * c) * ((c' * c⁻¹) * c) = 1 := by rw [← hc'c]; exact hc'
  obtain ⟨w, hw, hwc⟩ := exists_zpow_conj_of_odd hc hyc (odd_orderOf_of_mem_pPrimeCore hy)
  refine ⟨w, ?_, by rw [hwc]; exact hc'c.symm⟩
  exact (Subgroup.zpowers_le.2 hy) hw

end Basic

section TI

variable {C : Type} [Group C] [Finite C]

structure TIDataQ (v : C) (Zs : Set C) (S E : Subgroup C) (x : C) : Prop where
  v_sq : v * v = 1
  v_ne : v ≠ 1
  v_comm : ∀ c : C, c * v = v * c
  Z_sq : ∀ z ∈ Zs, z * z = 1
  Z_ne : ∀ z ∈ Zs, z ≠ 1
  v_nmem : v ∉ Zs
  Z_conj : ∀ z ∈ Zs, ∀ g : C, g * z * g⁻¹ ∈ Zs
  Z_mul_v : ∀ z ∈ Zs, z * v ∈ Zs
  sylow : IsSylowOf 2 S ⊤
  E_le : E ≤ S
  E_card : Nat.card E = 8
  E_comm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a
  E_sq : ∀ a ∈ E, a * a = 1
  v_mem : v ∈ E
  S_norm : ∀ s ∈ S, ∀ e ∈ E, s * e * s⁻¹ ∈ E
  Z_inter : ∀ y ∈ S, (y ∈ Zs ↔ (y ∈ E ∧ y ≠ 1 ∧ y ≠ v))
  x_Z : x ∈ Zs
  x_E : x ∈ E
  Z_single : ∀ z ∈ Zs, ∃ c : C, c * x * c⁻¹ = z
  cent : ∀ g : C, g * x = x * g → ∀ e ∈ E, ∃ e' ∈ E, ∃ o ∈ pPrimeCore 2 C, g * e * g⁻¹ = e' * o

variable {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

omit [Finite C] in
theorem card_map_mk_of_injOn {H : Subgroup C} (hH : ∀ a ∈ H, ∀ b ∈ H,
    (QuotientGroup.mk' (pPrimeCore 2 C)) a = (QuotientGroup.mk' (pPrimeCore 2 C)) b → a = b) :
    Nat.card ↥(H.map (QuotientGroup.mk' (pPrimeCore 2 C))) = Nat.card ↥H := by
  have h1 : Nat.card ↥(H.map (QuotientGroup.mk' (pPrimeCore 2 C))) =
      ((H.map (QuotientGroup.mk' (pPrimeCore 2 C)) : Subgroup (C ⧸ pPrimeCore 2 C)) :
        Set (C ⧸ pPrimeCore 2 C)).ncard :=
    Nat.card_coe_set_eq ((H.map (QuotientGroup.mk' (pPrimeCore 2 C)) : Subgroup (C ⧸ pPrimeCore 2 C)) :
        Set (C ⧸ pPrimeCore 2 C))
  have h2 : Nat.card ↥H = (H : Set C).ncard := Nat.card_coe_set_eq (H : Set C)
  rw [h1, h2, Subgroup.coe_map]
  exact Set.InjOn.ncard_image (fun a ha b hb hab => hH a ha b hb hab)

theorem tiData_quotient (h : TIDataQ v Zs S E x) :
    TIData (QuotientGroup.mk' (pPrimeCore 2 C) v) ((QuotientGroup.mk' (pPrimeCore 2 C)) '' Zs)
      (S.map (QuotientGroup.mk' (pPrimeCore 2 C))) (E.map (QuotientGroup.mk' (pPrimeCore 2 C)))
      (QuotientGroup.mk' (pPrimeCore 2 C) x) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  have hSp : IsPGroup 2 ↥S := h.sylow.isPGroup
  have hSinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b := fun a ha b hb hab => mk_injOn hSp ha hb hab
  have hEinj : ∀ a ∈ E, ∀ b ∈ E, π a = π b → a = b := fun a ha b hb hab =>
    hSinj a (h.E_le ha) b (h.E_le hb) hab
  have hker : ∀ c : C, π c = 1 ↔ c ∈ pPrimeCore 2 C := fun c => QuotientGroup.eq_one_iff c
  have hxsq := h.Z_sq x h.x_Z
  refine
    { v_sq := by rw [← map_mul, h.v_sq, map_one]
      v_ne := ?_
      v_comm := ?_
      Z_sq := ?_
      Z_ne := ?_
      v_nmem := ?_
      Z_conj := ?_
      Z_mul_v := ?_
      sylow := ?_
      E_le := Subgroup.map_mono h.E_le
      E_card := ?_
      E_comm := ?_
      E_sq := ?_
      v_mem := Subgroup.mem_map_of_mem _ h.v_mem
      S_norm := ?_
      Z_inter := ?_
      x_Z := Set.mem_image_of_mem _ h.x_Z
      x_E := Subgroup.mem_map_of_mem _ h.x_E
      Z_single := ?_
      cent := ?_ }
  · intro h1
    exact h.v_ne (eq_one_of_mem_pPrimeCore_of_sq ((hker v).1 h1) h.v_sq)
  · intro c
    obtain ⟨c, rfl⟩ := QuotientGroup.mk'_surjective _ c
    rw [← map_mul, ← map_mul, h.v_comm c]
  · rintro _ ⟨z, hz, rfl⟩
    rw [← map_mul, h.Z_sq z hz, map_one]
  · rintro _ ⟨z, hz, rfl⟩ h1
    exact h.Z_ne z hz (eq_one_of_mem_pPrimeCore_of_sq ((hker z).1 h1) (h.Z_sq z hz))
  · rintro ⟨z, hz, hzv⟩
    have h1 : v⁻¹ * z ∈ pPrimeCore 2 C := QuotientGroup.eq.1 hzv.symm
    have hzz := h.Z_sq z hz
    have hcomm : v⁻¹ * z = z * v⁻¹ := by
      have := h.v_comm z
      calc v⁻¹ * z = v⁻¹ * (z * v) * v⁻¹ := by group
        _ = v⁻¹ * (v * z) * v⁻¹ := by rw [this]
        _ = z * v⁻¹ := by group
    have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right h.v_sq
    have hsq : (v⁻¹ * z) * (v⁻¹ * z) = 1 := by
      calc (v⁻¹ * z) * (v⁻¹ * z) = v⁻¹ * (z * v⁻¹) * z := by group
        _ = v⁻¹ * (v⁻¹ * z) * z := by rw [← hcomm]
        _ = (v⁻¹ * v⁻¹) * (z * z) := by group
        _ = 1 := by rw [hvinv, h.v_sq, hzz, one_mul]
    have h2 := eq_one_of_mem_pPrimeCore_of_sq h1 hsq
    have : z = v := by
      calc z = v * (v⁻¹ * z) := by group
        _ = v := by rw [h2, mul_one]
    exact h.v_nmem (this ▸ hz)
  · rintro _ ⟨z, hz, rfl⟩ g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact ⟨g * z * g⁻¹, h.Z_conj z hz g, by rw [map_mul, map_mul, map_inv]⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact ⟨z * v, h.Z_mul_v z hz, by rw [map_mul]⟩
  ·
    have hcardS : Nat.card ↥(S.map π) = Nat.card ↥S := card_map_mk_of_injOn hSinj
    have hfac := h.sylow.card_eq
    rw [Subgroup.card_top] at hfac
    have hmul : Nat.card C = Nat.card (C ⧸ pPrimeCore 2 C) * Nat.card ↥(pPrimeCore 2 C) := by
      have := Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 C)
      exact this
    have hodd := odd_card_pPrimeCore (C := C)
    have hv2 : (Nat.card (C ⧸ pPrimeCore 2 C)).factorization 2 = (Nat.card C).factorization 2 := by
      have hne : ∀ n : ℕ, 0 < n → n ≠ 0 := fun n hn => hn.ne'
      have hpos1 : 0 < Nat.card (C ⧸ pPrimeCore 2 C) := Nat.card_pos
      have hpos2 : 0 < Nat.card ↥(pPrimeCore 2 C) := Nat.card_pos
      have h3 := congrArg (fun n => n.factorization 2) hmul
      simp only [Nat.factorization_mul (hne _ hpos1) (hne _ hpos2), Finsupp.add_apply] at h3
      have h4 : (Nat.card ↥(pPrimeCore 2 C)).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (fun hd => (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hd))
      omega
    refine isSylowOf_of_card le_top ?_
    rw [Subgroup.card_top, hcardS, hfac, hv2]
  · rw [card_map_mk_of_injOn hEinj, h.E_card]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, h.E_comm a ha b hb]
  · rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, h.E_sq a ha, map_one]
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨e, he, rfl⟩
    exact ⟨s * e * s⁻¹, h.S_norm s hs e he, by simp⟩
  · rintro _ ⟨y, hy, rfl⟩
    constructor
    · rintro ⟨z, hz, hzy⟩
      have hy2 : y * y = 1 := by
        have h1 : (y * y) ∈ pPrimeCore 2 C := by
          rw [← hker, map_mul, ← hzy, ← map_mul, h.Z_sq z hz, map_one]
        have h2 : y * y ∈ S := S.mul_mem hy hy
        have h3 : y * y ∈ S ⊓ pPrimeCore 2 C := ⟨h2, h1⟩
        rw [inf_pPrimeCore_eq_bot hSp, Subgroup.mem_bot] at h3
        exact h3
      have hyz : y⁻¹ * z ∈ pPrimeCore 2 C := QuotientGroup.eq.1 hzy.symm
      obtain ⟨w, -, hw⟩ := exists_conj_of_inv_mul_mem hy2 (h.Z_sq z hz) hyz
      have hyZ : y ∈ Zs := by
        have := h.Z_conj z hz w⁻¹
        rw [← hw] at this
        have e : w⁻¹ * (w * y * w⁻¹) * w⁻¹⁻¹ = y := by group
        rwa [e] at this
      obtain ⟨hyE, hy1, hyv⟩ := (h.Z_inter y hy).1 hyZ
      refine ⟨Subgroup.mem_map_of_mem _ hyE, ?_, ?_⟩
      · intro h1
        exact hy1 (hSinj y hy 1 S.one_mem (by rw [h1, map_one]))
      · intro h1
        exact hyv (hSinj y hy v (h.E_le h.v_mem) h1)
    · rintro ⟨⟨e, he, hey⟩, h1, h2⟩
      have hye : y = e := hSinj y hy e (h.E_le he) hey.symm
      subst hye
      refine ⟨y, (h.Z_inter y hy).2 ⟨he, ?_, ?_⟩, rfl⟩
      · intro h3
        exact h1 (by rw [h3, map_one])
      · intro h3
        exact h2 (by rw [h3])
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨c, hc⟩ := h.Z_single z hz
    exact ⟨π c, by rw [← map_inv, ← map_mul, ← map_mul, hc]⟩
  · intro g hg
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    have hg' : π (g * x * g⁻¹) = π x := by
      have h1 := hg
      rw [← map_mul, ← map_mul] at h1
      have h2 : π (g * x) = π (x * g) := h1
      rw [map_mul, map_mul] at h2
      rw [map_mul, map_mul, map_inv, h2]
      group
    have hinv : x⁻¹ * (g * x * g⁻¹) ∈ pPrimeCore 2 C := QuotientGroup.eq.1 hg'.symm
    have hgxsq : (g * x * g⁻¹) * (g * x * g⁻¹) = 1 := by
      calc (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
        _ = 1 := by rw [hxsq]; group
    obtain ⟨w, hwO, hw⟩ := exists_conj_of_inv_mul_mem hxsq hgxsq hinv
    set hh : C := w⁻¹ * g with hhh
    have hhx : hh * x = x * hh := by
      have : hh * x * hh⁻¹ = x := by
        calc hh * x * hh⁻¹ = w⁻¹ * (g * x * g⁻¹) * w := by rw [hhh]; group
          _ = w⁻¹ * (w * x * w⁻¹) * w := by rw [hw]
          _ = x := by group
      calc hh * x = (hh * x * hh⁻¹) * hh := by group
        _ = x * hh := by rw [this]
    rintro _ ⟨e, he, rfl⟩
    obtain ⟨e', he', o, ho, hhe⟩ := h.cent hh hhx e he
    refine ⟨e', he', ?_⟩
    have hπg : π g = π hh := by
      have : g = w * hh := by rw [hhh]; group
      rw [this, map_mul, (hker w).2 hwO, one_mul]
    have : π g * π e * (π g)⁻¹ = π e' := by
      rw [hπg, ← map_inv, ← map_mul, ← map_mul, hhe, map_mul, (hker o).2 ho, mul_one]
    exact this.symm

end TI

section Solv

theorem isSolvable_of_factorization_two_le_one {Y : Type} [Group Y] [Finite Y]
    (h : (Nat.card Y).factorization 2 ≤ 1) : Group.IsSolvable Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_cases hodd : Odd (Nat.card Y)
  · exact CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  · have heven : Even (Nat.card Y) := Nat.not_odd_iff_even.1 hodd
    obtain ⟨Q⟩ : Nonempty (Sylow 2 Y) := inferInstance
    have hQcard : Nat.card (Q : Subgroup Y) = 2 ^ (Nat.card Y).factorization 2 :=
      Sylow.card_eq_multiplicity Q
    have hcyc : IsCyclic (Q : Subgroup Y) := by
      rcases (show (Nat.card Y).factorization 2 = 0 ∨ (Nat.card Y).factorization 2 = 1 by omega)
        with hk | hk
      · rw [hk, pow_zero] at hQcard
        have : Subsingleton (Q : Subgroup Y) := (Nat.card_eq_one_iff_unique.1 hQcard).1
        exact isCyclic_of_subsingleton
      · rw [hk, pow_one] at hQcard
        exact isCyclic_of_prime_card hQcard
    have hnorm : normalizer (Q : Set Y) ≤ centralizer (Q : Set Y) :=
      IsCyclic.normalizer_le_centralizer ((Nat.minFac_eq_two_iff _).mpr
        (even_iff_two_dvd.mp heven)) hcyc
    let tr : Y →* (Q : Subgroup Y) := MonoidHom.transferSylow Q hnorm
    have hodd' : Odd (Nat.card tr.ker) :=
      Nat.not_even_iff_odd.1 fun he =>
        MonoidHom.not_dvd_card_ker_transferSylow Q hnorm (even_iff_two_dvd.1 he)
    have : Group.IsSolvable tr.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
    have : Group.IsSolvable (Q : Subgroup Y) :=
      Group.isSolvable_of_comm (fun a b => (IsCyclic.isMulCommutative : IsMulCommutative ↥Q).is_comm.comm a b)
    have : Group.IsSolvable (Y ⧸ tr.ker) :=
      Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective tr)
    exact Group.isSolvable_of_subgroup_quotient tr.ker

end Solv

section SolvE

variable {D : Type} [Group D] [Finite D]

theorem isSolvable_centralizer_of_card_eight {E S : Subgroup D}
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEcard : Nat.card E = 8)
    (hEn : ∀ g : D, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hSyl : IsSylowOf 2 S ⊤)
    (hCS : Nat.card ↥(S ⊓ centralizer (E : Set D)) ≤ 16) :
    Group.IsSolvable ↥(centralizer (E : Set D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₀ : Subgroup D := centralizer (E : Set D) with hK₀
  have hEK : E ≤ K₀ := fun e he => Subgroup.mem_centralizer_iff.2 fun h hh => hEcomm h hh e he
  have hK₀n : K₀.Normal := ⟨fun n hn g => by
    rw [hK₀, Subgroup.mem_centralizer_iff] at hn ⊢
    intro e he
    have h1 := hn (g⁻¹ * e * g) (by simpa using hEn g⁻¹ e he)
    calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * e := by group⟩
  set N₀ : Subgroup ↥K₀ := E.subgroupOf K₀ with hN₀
  have hN₀n : N₀.Normal := ⟨fun n hn g => by
    have hnE : ((n : K₀) : D) ∈ E := hn
    have hg : ∀ e ∈ E, e * (g : D) = (g : D) * e := fun e he =>
      Subgroup.mem_centralizer_iff.1 g.2 e he
    have : (g : D) * (n : D) * (g : D)⁻¹ = (n : D) := by
      rw [← hg _ hnE]; group
    show ((g * n * g⁻¹ : K₀) : D) ∈ E
    simpa [this] using hnE⟩
  have hN₀card : Nat.card N₀ = 8 := by
    rw [← hEcard]; exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEK).toEquiv
  have hsolvN : Group.IsSolvable ↥N₀ := Group.isSolvable_of_comm (fun a b => Subtype.ext
    (Subtype.ext (hEcomm _ (Subgroup.mem_subgroupOf.1 a.2) _ (Subgroup.mem_subgroupOf.1 b.2))))
  have hcardY : Nat.card ↥K₀ = Nat.card (↥K₀ ⧸ N₀) * 8 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N₀, hN₀card]
  have hR : IsSylowOf 2 (S ⊓ K₀) K₀ :=
    hSyl.inf_of_le_normalizer le_top (Subgroup.normalizer_eq_top_iff.2 hK₀n).ge
  have hf : (Nat.card ↥K₀).factorization 2 ≤ 4 := by
    have h1 : 2 ^ (Nat.card ↥K₀).factorization 2 ≤ 2 ^ 4 := by
      rw [← hR.card_eq]; exact hCS
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 h1
  have hfY : (Nat.card (↥K₀ ⧸ N₀)).factorization 2 ≤ 1 := by
    have hpos : 0 < Nat.card (↥K₀ ⧸ N₀) := Nat.card_pos
    have h8 : (8 : ℕ).factorization 2 = 3 := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [hcardY, Nat.factorization_mul hpos.ne' (by norm_num)] at hf
    simp only [Finsupp.add_apply, h8] at hf
    omega
  have : Group.IsSolvable (↥K₀ ⧸ N₀) := isSolvable_of_factorization_two_le_one hfY
  exact Group.isSolvable_of_subgroup_quotient N₀

omit [Finite D] in
theorem commutator_mem_centralizer {v : D} (hvc : ∀ c : D, c * v = v * c) {E : Subgroup D}
    {g h : D} (hg : ∀ e ∈ E, e⁻¹ * (g * e * g⁻¹) ∈ zpowers v)
    (hh : ∀ e ∈ E, e⁻¹ * (h * e * h⁻¹) ∈ zpowers v) :
    (g * h)⁻¹ * (h * g) ∈ centralizer (E : Set D) := by
  have hvZ : v ∈ center D := Subgroup.mem_center_iff.2 hvc
  have hZ : ∀ c ∈ zpowers v, ∀ y : D, y * c * y⁻¹ = c := fun c hc y => by
    have := Subgroup.mem_center_iff.1 ((zpowers_le.2 hvZ) hc) y
    rw [this]; group
  have hZc : ∀ c ∈ zpowers v, ∀ c' ∈ zpowers v, c * c' = c' * c := fun c hc c' hc' => by
    have := Subgroup.mem_center_iff.1 ((zpowers_le.2 hvZ) hc) c'
    exact this.symm
  rw [Subgroup.mem_centralizer_iff]
  intro e he
  obtain ⟨c₁, hc₁, hgc⟩ : ∃ c₁ ∈ zpowers v, g * e * g⁻¹ = e * c₁ :=
    ⟨e⁻¹ * (g * e * g⁻¹), hg e he, by group⟩
  obtain ⟨c₂, hc₂, hhc⟩ : ∃ c₂ ∈ zpowers v, h * e * h⁻¹ = e * c₂ :=
    ⟨e⁻¹ * (h * e * h⁻¹), hh e he, by group⟩
  have hAB : (g * h) * e * (g * h)⁻¹ = (h * g) * e * (h * g)⁻¹ := by
    calc (g * h) * e * (g * h)⁻¹ = g * (h * e * h⁻¹) * g⁻¹ := by group
      _ = (g * e * g⁻¹) * (g * c₂ * g⁻¹) := by rw [hhc]; group
      _ = (e * c₁) * c₂ := by rw [hgc, hZ c₂ hc₂]
      _ = (e * c₂) * c₁ := by rw [mul_assoc, hZc c₁ hc₁ c₂ hc₂, ← mul_assoc]
      _ = (h * g) * e * (h * g)⁻¹ := by
        rw [show (h * g) * e * (h * g)⁻¹ = h * (g * e * g⁻¹) * h⁻¹ by group, hgc,
          show h * (e * c₁) * h⁻¹ = (h * e * h⁻¹) * (h * c₁ * h⁻¹) by group, hhc, hZ c₁ hc₁]
  calc e * ((g * h)⁻¹ * (h * g)) = (g * h)⁻¹ * ((g * h) * e * (g * h)⁻¹) * (h * g) := by group
    _ = (g * h)⁻¹ * ((h * g) * e * (h * g)⁻¹) * (h * g) := by rw [hAB]
    _ = ((g * h)⁻¹ * (h * g)) * e := by group

theorem exists_two_pow_mul_three_pow_of_dvd_24 {n : ℕ} (h : n ∣ 24) : ∃ a b : ℕ, n = 2 ^ a * 3 ^ b := by
  have hn : n ∈ Nat.divisors 24 := Nat.mem_divisors.2 ⟨h, by norm_num⟩
  have hd : Nat.divisors 24 = {1, 2, 3, 4, 6, 8, 12, 24} := by decide
  rw [hd] at hn
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 0, by norm_num⟩
  · exact ⟨1, 0, by norm_num⟩
  · exact ⟨0, 1, by norm_num⟩
  · exact ⟨2, 0, by norm_num⟩
  · exact ⟨1, 1, by norm_num⟩
  · exact ⟨3, 0, by norm_num⟩
  · exact ⟨2, 1, by norm_num⟩
  · exact ⟨3, 1, by norm_num⟩

theorem isSolvable_of_normal_eight {v : D} {S E : Subgroup D}
    (hv2 : v * v = 1) (hv1 : v ≠ 1) (hvc : ∀ c : D, c * v = v * c)
    (hEcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a) (hEcard : Nat.card E = 8) (hvE : v ∈ E)
    (hEn : ∀ g : D, ∀ e ∈ E, g * e * g⁻¹ ∈ E) (hSyl : IsSylowOf 2 S ⊤)
    (hCS : Nat.card ↥(S ⊓ centralizer (E : Set D)) ≤ 16) : Group.IsSolvable D := by
  have hK₀solv := isSolvable_centralizer_of_card_eight hEcomm hEcard hEn hSyl hCS
  have hvZ : v ∈ center D := Subgroup.mem_center_iff.2 hvc
  have hZn : (zpowers v).Normal := ⟨fun n hn g => by
    have hn' := Subgroup.mem_center_iff.1 ((zpowers_le.2 hvZ) hn) g
    have : g * n * g⁻¹ = n := by rw [hn']; group
    rw [this]; exact hn⟩
  set π : D →* D ⧸ zpowers v := QuotientGroup.mk' (zpowers v) with hπ
  set Eb : Subgroup (D ⧸ zpowers v) := E.map π with hEb
  have hEbcard : Nat.card Eb = 4 := by
    have h1 : Nat.card Eb * 2 = Nat.card E :=
      card_map_mk_mul_two (v := v) hv2 hv1 E (zpowers_le.2 hvE)
    rw [hEcard] at h1
    omega
  have hEbn : Eb.Normal := ⟨fun n hn g => by
    obtain ⟨e, he, rfl⟩ := hn
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ g
    exact ⟨g * e * g⁻¹, hEn g e he, by simp [π, map_mul, map_inv]⟩⟩
  let ρ : D →* Equiv.Perm ↥Eb := (MulAut.toPerm ↥Eb).comp ((MulAut.conjNormal (H := Eb)).comp π)
  set K₁ : Subgroup D := ρ.ker with hK₁
  have hK₁n : K₁.Normal := MonoidHom.normal_ker ρ
  have hK₁act : ∀ g ∈ K₁, ∀ e ∈ E, e⁻¹ * (g * e * g⁻¹) ∈ zpowers v := by
    intro g hg e he
    have h1 : ρ g = 1 := hg
    have h2 : ((ρ g ⟨π e, Subgroup.mem_map_of_mem _ he⟩ : Eb) : D ⧸ zpowers v) =
        π (g * e * g⁻¹) := by
      show π g * π e * (π g)⁻¹ = _
      rw [map_mul, map_mul, map_inv]
    rw [h1] at h2
    have h3 : π e = π (g * e * g⁻¹) := h2
    exact QuotientGroup.eq.1 h3
  have hK₀K₁ : centralizer (E : Set D) ≤ K₁ := by
    intro g hg
    show ρ g = 1
    refine Equiv.ext fun b => Subtype.ext ?_
    obtain ⟨b, hb⟩ := b
    obtain ⟨e, he, rfl⟩ := hb
    show π g * π e * (π g)⁻¹ = π e
    rw [← map_mul, ← map_inv, ← map_mul]
    have : g * e * g⁻¹ = e := by
      rw [← Subgroup.mem_centralizer_iff.1 hg e he]; group
    rw [this]
  have hK₀n : (centralizer (E : Set D)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_centralizer_iff] at hn ⊢
    intro e he
    have h1 := hn (g⁻¹ * e * g) (by simpa using hEn g⁻¹ e he)
    calc e * (g * n * g⁻¹) = g * ((g⁻¹ * e * g) * n) * g⁻¹ := by group
      _ = g * (n * (g⁻¹ * e * g)) * g⁻¹ := by rw [h1]
      _ = (g * n * g⁻¹) * e := by group⟩
  have hK₁solv : Group.IsSolvable ↥K₁ := by
    set N₁ : Subgroup ↥K₁ := (centralizer (E : Set D)).subgroupOf K₁ with hN₁
    have hN₁n : N₁.Normal := hK₀n.subgroupOf K₁
    have hN₁solv : Group.IsSolvable ↥N₁ :=
      Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hK₀K₁).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hK₀K₁).injective
    have hcomm : ∀ a b : ↥K₁ ⧸ N₁, a * b = b * a := by
      intro a b
      induction a using QuotientGroup.induction_on with | H a =>
      induction b using QuotientGroup.induction_on with | H b =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      exact commutator_mem_centralizer hvc (hK₁act a a.2) (hK₁act b b.2)
    have : Group.IsSolvable (↥K₁ ⧸ N₁) := Group.isSolvable_of_comm hcomm
    exact Group.isSolvable_of_subgroup_quotient N₁
  have hdvd : Nat.card (D ⧸ K₁) ∣ 24 := by
    have h1 : Nat.card (Equiv.Perm ↥Eb) = 24 := by
      rw [Nat.card_perm, hEbcard]; rfl
    rw [← h1]
    exact Subgroup.card_dvd_of_injective (QuotientGroup.kerLift ρ) (QuotientGroup.kerLift_injective ρ)
  obtain ⟨a, b, hab⟩ := exists_two_pow_mul_three_pow_of_dvd_24 hdvd
  have hKq : Group.IsSolvable (D ⧸ K₁) := by
    have : Fintype (D ⧸ K₁) := Fintype.ofFinite _
    exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
      Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact hab)
  exact Group.isSolvable_of_subgroup_quotient K₁

end SolvE

section Final

variable {C : Type} [Group C] [Finite C] {v : C} {Zs : Set C} {S E : Subgroup C} {x : C}

theorem normalizer_map_eq_top (hZD : S_ZD) (h : TIDataQ v Zs S E x)
    (hS : Nat.card S ≤ 128) (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v) :
    normalizer (↑(E.map (QuotientGroup.mk' (pPrimeCore 2 C))) : Set (C ⧸ pPrimeCore 2 C)) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  have hSp : IsPGroup 2 ↥S := h.sylow.isPGroup
  have hSinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b := fun a ha b hb hab => mk_injOn hSp ha hb hab
  have hT := tiData_quotient h
  have hS' : Nat.card ↥(S.map π) ≤ 128 := by
    rw [card_map_mk_of_injOn hSinj]; exact hS
  have hex' : ∃ s ∈ S.map π, s * s = 1 ∧ s ∉ E.map π := by
    obtain ⟨s, hsS, hs2, hsE⟩ := hex
    refine ⟨π s, ⟨s, hsS, rfl⟩, by rw [← map_mul, hs2, map_one], ?_⟩
    rintro ⟨e, he, hes⟩
    exact hsE (hSinj e (h.E_le he) s hsS hes ▸ he)
  have hZS' : ∀ s ∈ S.map π, (∀ t ∈ S.map π, s * t = t * s) → s * s = 1 → s ≠ 1 → s = π v := by
    rintro _ ⟨s, hsS, rfl⟩ hcomm hsq hs1
    have hsc : ∀ t ∈ S, s * t = t * s := by
      intro t ht
      apply hSinj _ (S.mul_mem hsS ht) _ (S.mul_mem ht hsS)
      rw [map_mul, map_mul]
      exact hcomm _ ⟨t, ht, rfl⟩
    have hs2 : s * s = 1 := by
      apply hSinj _ (S.mul_mem hsS hsS) _ S.one_mem
      rw [map_mul, map_one]; exact hsq
    have hs1' : s ≠ 1 := fun h1 => hs1 (by rw [h1, map_one])
    rw [hZS s hsS hsc hs2 hs1']
  exact normalizer_eq_top hZD hT hS' hex' hZS'

theorem isSolvable_of_tiDataQ (hZD : S_ZD) (h : TIDataQ v Zs S E x)
    (hS : Nat.card S ≤ 128) (hex : ∃ s ∈ S, s * s = 1 ∧ s ∉ E)
    (hZS : ∀ s ∈ S, (∀ t ∈ S, s * t = t * s) → s * s = 1 → s ≠ 1 → s = v)
    (hCS : Nat.card ↥(S ⊓ centralizer (E : Set C)) ≤ 16) : Group.IsSolvable C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  have hSp : IsPGroup 2 ↥S := h.sylow.isPGroup
  have hSinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b := fun a ha b hb hab => mk_injOn hSp ha hb hab
  have hT := tiData_quotient h
  have hN : normalizer (↑(E.map π) : Set (C ⧸ pPrimeCore 2 C)) = ⊤ :=
    normalizer_map_eq_top hZD h hS hex hZS
  have hEn : ∀ g : C ⧸ pPrimeCore 2 C, ∀ e ∈ E.map π, g * e * g⁻¹ ∈ E.map π := fun g e he =>
    (Subgroup.mem_normalizer_iff.1 (hN ▸ Subgroup.mem_top g) e).1 he
  have hCS' : Nat.card ↥(S.map π ⊓ centralizer (↑(E.map π) : Set (C ⧸ pPrimeCore 2 C))) ≤ 16 := by
    have hEq : S.map π ⊓ centralizer (↑(E.map π) : Set (C ⧸ pPrimeCore 2 C)) =
        (S ⊓ centralizer (E : Set C)).map π := by
      apply le_antisymm
      · rintro _ ⟨⟨s, hsS, rfl⟩, hsc⟩
        have hsc' : π s ∈ centralizer (↑(E.map π) : Set (C ⧸ pPrimeCore 2 C)) := hsc
        refine ⟨s, ⟨hsS, ?_⟩, rfl⟩
        show s ∈ centralizer (E : Set C)
        rw [Subgroup.mem_centralizer_iff]
        intro e he
        apply hSinj _ (S.mul_mem (h.E_le he) hsS) _ (S.mul_mem hsS (h.E_le he))
        rw [map_mul, map_mul]
        exact Subgroup.mem_centralizer_iff.1 hsc' (π e) ⟨e, he, rfl⟩
      · rintro _ ⟨s, ⟨hsS, hsc⟩, rfl⟩
        have hsc' : s ∈ centralizer (E : Set C) := hsc
        refine ⟨⟨s, hsS, rfl⟩, ?_⟩
        show π s ∈ centralizer (↑(E.map π) : Set (C ⧸ pPrimeCore 2 C))
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨e, he, rfl⟩
        rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.1 hsc' e he]
    rw [hEq, card_map_mk_of_injOn (H := S ⊓ centralizer (E : Set C))
      (fun a ha b hb hab => hSinj a ha.1 b hb.1 hab)]
    exact hCS
  have hDsolv : Group.IsSolvable (C ⧸ pPrimeCore 2 C) :=
    isSolvable_of_normal_eight hT.v_sq hT.v_ne hT.v_comm hT.E_comm hT.E_card hT.v_mem hEn hT.sylow hCS'
  have hOsolv : Group.IsSolvable ↥(pPrimeCore 2 C) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ odd_card_pPrimeCore
  exact Group.isSolvable_of_subgroup_quotient (pPrimeCore 2 C)

end Final

end CFSG.GH74.GLS.Th2.P412
