module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesL630Apply

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem centralizer_le_of_three_dvd {M : Subgroup G} (hM : GLBStronglyEmbedded 3 M) {m : G}
    (hmM : m ∈ M) (h3 : 3 ∣ orderOf m) : centralizer ({m} : Set G) ≤ M := by
  intro g hg
  by_contra hgM
  have hgm : g * m = m * g := mem_centralizer_singleton_iff.mp hg
  have hmem : m ∈ M ⊓ GLBConj g M := by
    refine ⟨hmM, Subgroup.mem_map.mpr ⟨m, hmM, ?_⟩⟩
    show g⁻¹ * m * g⁻¹⁻¹ = m
    rw [inv_inv]
    calc g⁻¹ * m * g = g⁻¹ * (m * g) := by group
      _ = g⁻¹ * (g * m) := by rw [← hgm]
      _ = m := by group
  have hdvd := orderOf_dvd_natCard (⟨m, hmem⟩ : ↥(M ⊓ GLBConj g M))
  rw [orderOf_mk] at hdvd
  exact hM.2.2 g hgM (h3.trans hdvd)

theorem mem_map_conj_iff {K : Subgroup G} {l y : G} :
    y ∈ K.map (MulAut.conj l).toMonoidHom ↔ l⁻¹ * y * l ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : l⁻¹ * ((MulAut.conj l).toMonoidHom k) * l = k := by
      show l⁻¹ * (l * k * l⁻¹) * l = k
      group
    rw [this]
    exact hk
  · intro h
    refine ⟨l⁻¹ * y * l, h, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem exists_conj_eq_of_card_five {L A B : Subgroup G} (hAL : A ≤ L) (hBL : B ≤ L)
    (hA : Nat.card A = 5) (hB : Nat.card B = 5)
    (hsyl : ∀ D : Subgroup G, D ≤ L → IsPGroup 5 D → Nat.card D ≤ 5) :
    ∃ l ∈ L, B.map (MulAut.conj l).toMonoidHom = A := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hSyl : ∀ Q : Sylow 5 L, Nat.card (Q : Subgroup L) ≤ 5 := by
    intro Q
    have hinj : Function.Injective (L.subtype) := L.subtype_injective
    have hD : ((Q : Subgroup L).map L.subtype) ≤ L := Subgroup.map_subtype_le _
    have hpD : IsPGroup 5 ((Q : Subgroup L).map L.subtype) :=
      Q.isPGroup'.map L.subtype
    have hc := Subgroup.card_map_of_injective (K := (Q : Subgroup L)) hinj
    rw [← hc]
    exact hsyl _ hD hpD
  set AL : Subgroup L := A.subgroupOf L with hAL'
  set BL : Subgroup L := B.subgroupOf L with hBL'
  have hcAL : Nat.card AL = 5 := by
    rw [hAL', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAL).toEquiv, hA]
  have hcBL : Nat.card BL = 5 := by
    rw [hBL', Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB]
  obtain ⟨SA, hSA⟩ := (IsPGroup.of_card (p := 5) (n := 1)
    (by rw [hcAL]; norm_num)).exists_le_sylow
  obtain ⟨SB, hSB⟩ := (IsPGroup.of_card (p := 5) (n := 1)
    (by rw [hcBL]; norm_num)).exists_le_sylow
  have hSAeq : (SA : Subgroup L) = AL :=
    (Subgroup.eq_of_le_of_card_ge hSA (by rw [hcAL]; exact hSyl SA)).symm
  have hSBeq : (SB : Subgroup L) = BL :=
    (Subgroup.eq_of_le_of_card_ge hSB (by rw [hcBL]; exact hSyl SB)).symm
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq L SA SB
  have hgSA : ((g • SA : Sylow 5 L) : Subgroup L) = (SB : Subgroup L) := by rw [hg]
  have hAB : ∀ y ∈ A, (g : G) * y * (g : G)⁻¹ ∈ B := by
    intro y hy
    have hyL : y ∈ L := hAL hy
    have hyS : (⟨y, hyL⟩ : L) ∈ (SA : Subgroup L) := by
      rw [hSAeq, hAL']
      exact Subgroup.mem_subgroupOf.mpr hy
    have h1 : MulAut.conj g (⟨y, hyL⟩ : L) ∈ ((g • SA : Sylow 5 L) : Subgroup L) := by
      rw [Sylow.coe_subgroup_smul]
      exact Subgroup.smul_mem_pointwise_smul _ _ _ hyS
    rw [hgSA, hSBeq] at h1
    have h2 := Subgroup.mem_subgroupOf.mp h1
    simpa [MulAut.conj_apply] using h2
  have hmapA : A.map (MulAut.conj (g : G)).toMonoidHom ≤ B := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have := hAB y hy
    simpa [MulAut.conj_apply] using this
  have hcmap : Nat.card (A.map (MulAut.conj (g : G)).toMonoidHom) = 5 := by
    have hinj : Function.Injective (MulAut.conj (g : G)).toMonoidHom :=
      (MulAut.conj (g : G)).injective
    rw [Subgroup.card_map_of_injective hinj, hA]
  have hmapEq : A.map (MulAut.conj (g : G)).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hmapA (by rw [hcmap, hB])
  refine ⟨(g : G)⁻¹, ?_, ?_⟩
  · exact L.inv_mem g.2
  · have hcomp : (MulAut.conj (g : G)⁻¹).toMonoidHom.comp (MulAut.conj (g : G)).toMonoidHom
        = MonoidHom.id G := by
      ext y
      simp [MulAut.conj_apply, mul_assoc]
    rw [← hmapEq, Subgroup.map_map, hcomp, Subgroup.map_id]

theorem covering_of_involution {F : Subgroup G} {x c : G}
    (hodd : Odd (Nat.card (centralizer (F : Set G))))
    (hc2 : c ^ 2 = 1) (hc1 : c ≠ 1) (hcN : c ∈ normalizer (F : Set G))
    (hcC : c ∉ centralizer (F : Set G)) (hcF : ∀ a ∈ F, c * a * c⁻¹ = a⁻¹)
    (hxC : x ∈ centralizer (F : Set G)) (hxc : x * c = c * x) (hx5 : orderOf x = 5)
    (hsyl : ∀ D : Subgroup G, D ≤ centralizer (F : Set G) → IsPGroup 5 D → Nat.card D ≤ 5) :
    ∀ g ∈ normalizer (F : Set G), ∃ d ∈ centralizer (F : Set G), ∃ a ∈ normalizer (F : Set G),
      g = d * a ∧ a * c = c * a ∧ a ∈ normalizer ((zpowers x : Subgroup G) : Set G) := by
  classical
  set N : Subgroup G := normalizer (F : Set G) with hNdef
  set C : Subgroup G := centralizer (F : Set G) with hCdef
  have hC_le_N : C ≤ N := Subgroup.centralizer_le_normalizer _
  haveI hCn : (C.subgroupOf N).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_centralizer_of_mem_normalizer g.2 hn⟩
  have hodd' : Odd (Nat.card (C.subgroupOf N)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC_le_N).toEquiv]
    exact hodd
  have hcinv_eq : c⁻¹ = c := inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hc2)
  have hcinv' : ∀ a ∈ F, c⁻¹ * a * c = a⁻¹ := fun a ha => by
    have := hcF a ha
    rw [hcinv_eq] at this ⊢
    exact this
  have hcN' : c ∈ N := hcN
  have hc'2 : (⟨c, hcN'⟩ : N) ^ 2 = 1 := Subtype.ext (by simpa using hc2)
  have hc'C : (⟨c, hcN'⟩ : N) ∉ C.subgroupOf N := fun h => hcC (Subgroup.mem_subgroupOf.mp h)
  have hinv' : ∀ n : N, ∃ e ∈ C.subgroupOf N, n * (⟨c, hcN'⟩ : N) * n⁻¹ = e * ⟨c, hcN'⟩ := by
    intro n
    have ht : ∀ a ∈ F, ((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹ = a⁻¹ := by
      intro a ha
      have ha' : (n : G)⁻¹ * a * (n : G) ∈ F := (Subgroup.mem_normalizer_iff''.mp n.2 a).mp ha
      have h1 := hcF _ ha'
      calc ((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹
          = (n : G) * (c * ((n : G)⁻¹ * a * (n : G)) * c⁻¹) * (n : G)⁻¹ := by group
        _ = (n : G) * ((n : G)⁻¹ * a * (n : G))⁻¹ * (n : G)⁻¹ := by rw [h1]
        _ = a⁻¹ := by group
    have hec : (n : G) * c * (n : G)⁻¹ * c⁻¹ ∈ C := by
      rw [hCdef, mem_centralizer_iff]
      intro a ha
      have key : ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹ = a := by
        calc ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹
            = ((n : G) * c * (n : G)⁻¹) * (c⁻¹ * a * c) * ((n : G) * c * (n : G)⁻¹)⁻¹ := by
              group
          _ = ((n : G) * c * (n : G)⁻¹) * a⁻¹ * ((n : G) * c * (n : G)⁻¹)⁻¹ := by
              rw [hcinv' a ha]
          _ = (((n : G) * c * (n : G)⁻¹) * a * ((n : G) * c * (n : G)⁻¹)⁻¹)⁻¹ := by group
          _ = a := by rw [ht a ha, inv_inv]
      calc a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)
          = (((n : G) * c * (n : G)⁻¹ * c⁻¹) * a * ((n : G) * c * (n : G)⁻¹ * c⁻¹)⁻¹) *
              ((n : G) * c * (n : G)⁻¹ * c⁻¹) := by rw [key]
        _ = ((n : G) * c * (n : G)⁻¹ * c⁻¹) * a := by group
    refine ⟨⟨(n : G) * c * (n : G)⁻¹ * c⁻¹,
      N.mul_mem (N.mul_mem (N.mul_mem n.2 hcN') (N.inv_mem n.2)) (N.inv_mem hcN')⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hec
    · apply Subtype.ext
      show (n : G) * c * (n : G)⁻¹ = ((n : G) * c * (n : G)⁻¹ * c⁻¹) * c
      group
  intro g hg
  obtain ⟨d₁, hd₁, m, hm, hgdm⟩ :=
    mem_mul_centralizer_of_involution (H := ↥N) (C.subgroupOf N) hodd' hc'2 hc'C hinv' ⟨g, hg⟩
  have hgdm' : g = (d₁ : G) * (m : G) := by
    have := congrArg Subtype.val hgdm
    simpa using this
  have hmc : (m : G) * c * (m : G)⁻¹ = c := by
    have := congrArg Subtype.val hm
    simpa using this
  have hmc' : (m : G) * c = c * (m : G) := by
    calc (m : G) * c = ((m : G) * c * (m : G)⁻¹) * (m : G) := by group
      _ = c * (m : G) := by rw [hmc]
  have hd₁C : (d₁ : G) ∈ C := Subgroup.mem_subgroupOf.mp hd₁
  have hmN : (m : G) ∈ N := m.2
  set L : Subgroup G := C ⊓ centralizer ({c} : Set G) with hLdef
  set A : Subgroup G := zpowers x with hAdef
  set B : Subgroup G := A.map (MulAut.conj (m : G)).toMonoidHom with hBdef
  have hAL : A ≤ L := by
    rw [hAdef]
    refine zpowers_le.mpr ⟨hxC, ?_⟩
    exact mem_centralizer_singleton_iff.mpr hxc
  have hBL : B ≤ L := by
    intro b hb
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hb
    have hyL := hAL hy
    have hyC : y ∈ C := hyL.1
    have hyc : y * c = c * y := mem_centralizer_singleton_iff.mp hyL.2
    refine ⟨?_, ?_⟩
    · show (MulAut.conj (m : G)) y ∈ C
      rw [MulAut.conj_apply]
      exact conj_mem_centralizer_of_mem_normalizer hmN hyC
    · refine mem_centralizer_singleton_iff.mpr ?_
      show (MulAut.conj (m : G)) y * c = c * (MulAut.conj (m : G)) y
      rw [MulAut.conj_apply]
      have hmcinv : (m : G)⁻¹ * c = c * (m : G)⁻¹ := by
        calc (m : G)⁻¹ * c = (m : G)⁻¹ * (c * (m : G)) * (m : G)⁻¹ := by group
          _ = (m : G)⁻¹ * ((m : G) * c) * (m : G)⁻¹ := by rw [hmc']
          _ = c * (m : G)⁻¹ := by group
      calc (m : G) * y * (m : G)⁻¹ * c = (m : G) * y * ((m : G)⁻¹ * c) := by group
        _ = (m : G) * y * (c * (m : G)⁻¹) := by rw [hmcinv]
        _ = (m : G) * (y * c) * (m : G)⁻¹ := by group
        _ = (m : G) * (c * y) * (m : G)⁻¹ := by rw [hyc]
        _ = ((m : G) * c) * y * (m : G)⁻¹ := by group
        _ = (c * (m : G)) * y * (m : G)⁻¹ := by rw [hmc']
        _ = c * ((m : G) * y * (m : G)⁻¹) := by group
  have hA5 : Nat.card A = 5 := by
    rw [hAdef, Nat.card_zpowers, hx5]
  have hB5 : Nat.card B = 5 := by
    have hinj : Function.Injective (MulAut.conj (m : G)).toMonoidHom :=
      (MulAut.conj (m : G)).injective
    rw [hBdef, Subgroup.card_map_of_injective hinj, hA5]
  have hsylL : ∀ D : Subgroup G, D ≤ L → IsPGroup 5 D → Nat.card D ≤ 5 :=
    fun D hD hp => hsyl D (hD.trans inf_le_left) hp
  obtain ⟨l, hl, hlB⟩ := exists_conj_eq_of_card_five hAL hBL hA5 hB5 hsylL
  have hlC : l ∈ C := hl.1
  have hlc : l * c = c * l := mem_centralizer_singleton_iff.mp hl.2
  have hlN : l ∈ N := hC_le_N hlC
  refine ⟨d₁ * l⁻¹, C.mul_mem hd₁C (C.inv_mem hlC), l * (m : G), N.mul_mem hlN hmN, ?_, ?_, ?_⟩
  · rw [hgdm']
    group
  · calc (l * (m : G)) * c = l * ((m : G) * c) := by group
      _ = l * (c * (m : G)) := by rw [hmc']
      _ = (l * c) * (m : G) := by group
      _ = (c * l) * (m : G) := by rw [hlc]
      _ = c * (l * (m : G)) := by group
  ·
    rw [mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have h1 : (m : G) * h * (m : G)⁻¹ ∈ B := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      have h2 : l * ((m : G) * h * (m : G)⁻¹) * l⁻¹ ∈ B.map (MulAut.conj l).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨_, h1, rfl⟩
      rw [hlB] at h2
      have h3 : l * ((m : G) * h * (m : G)⁻¹) * l⁻¹ = (l * (m : G)) * h * (l * (m : G))⁻¹ := by
        group
      rw [← h3]
      exact h2
    · intro hh
      have h3 : (l * (m : G)) * h * (l * (m : G))⁻¹ ∈ A := hh
      rw [← hlB, mem_map_conj_iff] at h3
      have h4 : l⁻¹ * ((l * (m : G)) * h * (l * (m : G))⁻¹) * l = (m : G) * h * (m : G)⁻¹ := by
        group
      rw [h4] at h3
      rw [hBdef, mem_map_conj_iff] at h3
      have h5 : (m : G)⁻¹ * ((m : G) * h * (m : G)⁻¹) * (m : G) = h := by group
      rw [h5] at h3
      exact h3

theorem exists_exponent_four {x a : G} (hx5 : orderOf x = 5)
    (ha : a ∈ normalizer ((zpowers x : Subgroup G) : Set G)) :
    ∃ j : ℤ, a * x * a⁻¹ = x ^ j ∧ x ^ (j ^ 4) = x := by
  have hmem : a * x * a⁻¹ ∈ zpowers x := (mem_normalizer_iff.mp ha x).mp (mem_zpowers x)
  obtain ⟨j, hj⟩ := mem_zpowers_iff.mp hmem
  refine ⟨j, hj.symm, ?_⟩
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx5
    norm_num at hx5
  have h5j : ¬ (5 : ℤ) ∣ j := by
    intro h5
    have h1 : x ^ j = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hx5]
      exact_mod_cast h5
    rw [h1] at hj
    apply hx1
    calc x = a⁻¹ * (a * x * a⁻¹) * a := by group
      _ = 1 := by rw [← hj]; group
  have hj4 : ((j : ZMod 5)) ^ 4 = 1 := by
    have hne : (j : ZMod 5) ≠ 0 := by
      intro h
      apply h5j
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd j 5).mp h
      exact_mod_cast this
    have key : ∀ r : ZMod 5, r ≠ 0 → r ^ 4 = 1 := by decide
    exact key _ hne
  have hdiv : (5 : ℤ) ∣ j ^ 4 - 1 := by
    have h0 : (((j ^ 4 - 1 : ℤ)) : ZMod 5) = 0 := by
      push_cast
      rw [hj4, sub_self]
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (j ^ 4 - 1) 5).mp h0
    exact_mod_cast this
  have hx41 : x ^ (j ^ 4 - 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hx5]
    exact_mod_cast hdiv
  calc x ^ (j ^ 4) = x ^ ((j ^ 4 - 1) + 1) := by ring_nf
    _ = x ^ (j ^ 4 - 1) * x := zpow_add_one x _
    _ = x := by rw [hx41, one_mul]

theorem pow_four_mem_centralizer {x a : G} (hx5 : orderOf x = 5)
    (ha : a ∈ normalizer ((zpowers x : Subgroup G) : Set G)) :
    a ^ 4 ∈ centralizer ({x} : Set G) := by
  obtain ⟨j, hj, hj4⟩ := exists_exponent_four hx5 ha
  have hpow : ∀ n : ℕ, a ^ n * x * (a ^ n)⁻¹ = x ^ (j ^ n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc a ^ (n + 1) * x * (a ^ (n + 1))⁻¹ = a * (a ^ n * x * (a ^ n)⁻¹) * a⁻¹ := by
            rw [pow_succ']; group
        _ = a * x ^ (j ^ n) * a⁻¹ := by rw [ih]
        _ = (a * x * a⁻¹) ^ (j ^ n) := by rw [conj_zpow]
        _ = (x ^ j) ^ (j ^ n) := by rw [hj]
        _ = x ^ (j ^ (n + 1)) := by rw [← zpow_mul, pow_succ, mul_comm]
  rw [mem_centralizer_singleton_iff]
  have h4 := hpow 4
  rw [hj4] at h4
  calc a ^ 4 * x = (a ^ 4 * x * (a ^ 4)⁻¹) * a ^ 4 := by group
    _ = x * a ^ 4 := by rw [h4]

theorem conj_mem_centralizer_of_normalizer_zpowers {x a w : G} (hx5 : orderOf x = 5)
    (ha : a ∈ normalizer ((zpowers x : Subgroup G) : Set G))
    (hw : w ∈ centralizer ({x} : Set G)) :
    a * w * a⁻¹ ∈ centralizer ({x} : Set G) := by
  obtain ⟨j, hj, hj4⟩ := exists_exponent_four hx5 ha
  have hwx : w * x = x * w := mem_centralizer_singleton_iff.mp hw
  have hcomm : Commute (a * w * a⁻¹) (x ^ j) := by
    rw [← hj]
    show (a * w * a⁻¹) * (a * x * a⁻¹) = (a * x * a⁻¹) * (a * w * a⁻¹)
    calc (a * w * a⁻¹) * (a * x * a⁻¹) = a * (w * x) * a⁻¹ := by group
      _ = a * (x * w) * a⁻¹ := by rw [hwx]
      _ = (a * x * a⁻¹) * (a * w * a⁻¹) := by group
  have hx : x = (x ^ j) ^ (j ^ 3) := by
    rw [← zpow_mul, show j * j ^ 3 = j ^ 4 by ring, hj4]
  rw [mem_centralizer_singleton_iff]
  have hc2 : Commute (a * w * a⁻¹) ((x ^ j) ^ (j ^ 3)) := hcomm.zpow_right (j ^ 3)
  rw [← hx] at hc2
  exact hc2

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L630
