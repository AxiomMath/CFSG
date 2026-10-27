module

public import CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977Commuting
public import CFSG.LocalAnalysis.ZStar
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics

public section

namespace CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977

open CFSG.Assembly CFSG.Assembly.ComponentType

variable {G : Type*} [Group G]

theorem conj_inv_mem_normalizer_of_mem {H : Subgroup G} {g v : G}
    (hv : v ∈ Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    g⁻¹ * v * g ∈ Subgroup.normalizer (H : Set G) := by
  rw [← Subgroup.map_normalizer_eq_of_bijective H (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).bijective] at hv
  exact mem_conj_iff.mp hv

theorem isCyclic_and_card_le_of_le_conj [Finite G] {C : Subgroup G} (S : Sylow 2 C)
    (hS : IsCyclic S) {g : G} {P : Subgroup G} (hPC : P ≤ C.map (MulAut.conj g).toMonoidHom)
    (hP : IsPGroup 2 P) : IsCyclic P ∧ Nat.card P ≤ Nat.card S := by
  have hP'C : P.map (MulAut.conj g⁻¹).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    have := mem_conj_iff.mp (hPC hx)
    simpa [MulAut.conj_apply] using this
  let e : P ≃* P.map (MulAut.conj g⁻¹).toMonoidHom :=
    P.equivMapOfInjective _ (MulAut.conj g⁻¹).injective
  obtain ⟨hcyc, hcard⟩ := isCyclic_and_card_le_of_le S hS hP'C (hP.of_equiv e)
  exact ⟨isCyclic_of_injective e.toMonoidHom e.injective,
    (Nat.card_congr e.toEquiv).trans_le hcard⟩

theorem inf_centralizer_le_centralizer [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (hS : IsCyclic S) {g : G}
    (hg : g ∉ Subgroup.normalizer (L : Set G)) {Y : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (L : Set G)) (hY : IsPGroup 2 Y)
    (hT : 4 ≤ Nat.card (Y ⊓ (Subgroup.centralizer (L : Set G)).map
      (MulAut.conj g).toMonoidHom : Subgroup G)) :
    Y ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.centralizer
        ((Y ⊓ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Subgroup G) :
          Set G) ∧
      Y ⊓ Subgroup.centralizer (L : Set G) ≤ Subgroup.normalizer
        ((Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL' := hL
  obtain ⟨-, -, hodd, hNC, -⟩ := hL'
  set Cg := (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom with hCgdef
  set T := Y ⊓ Cg with hTdef
  set R := Y ⊓ Subgroup.centralizer (L : Set G) with hRdef
  have hTp : IsPGroup 2 T := hY.to_le inf_le_left
  have hRp : IsPGroup 2 R := hY.to_le inf_le_left
  have hRcyc : IsCyclic R := (isCyclic_and_card_le_of_le S hS inf_le_right hRp).1
  have hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := by
    intro a ha b hb
    have h := (IsCyclic.isMulCommutative (α := R)).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩
    simpa using congrArg Subtype.val h
  have hTcyc : IsCyclic T := (isCyclic_and_card_le_of_le_conj S hS inf_le_right hTp).1
  obtain ⟨⟨s, hsT⟩, hgen⟩ := IsCyclic.exists_generator (α := T)
  have hsord : orderOf s = Nat.card T := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hgen
    rwa [Subgroup.orderOf_mk] at h
  have hTzp : ∀ x ∈ T, ∃ k : ℤ, s ^ k = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨x, hx⟩)
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hsY : s ∈ Y := (Subgroup.mem_inf.mp hsT).1
  have hsR : s ∈ Subgroup.normalizer (R : Set G) := by
    have h1 : s ∈ Subgroup.normalizer (Y : Set G) := Subgroup.le_normalizer hsY
    have h2 : s ∈ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) :=
      hNC ▸ hYN hsY
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h1, h2⟩
  have hs2ne : s ^ 2 ≠ 1 := by
    intro h
    have h' := orderOf_dvd_of_pow_eq_one h
    rw [hsord] at h'
    have := Nat.le_of_dvd (by norm_num) h'
    omega
  have hs2T : s ^ 2 ∈ T := Subgroup.pow_mem _ hsT 2
  have hs2even : Even (orderOf (s ^ 2)) := by
    have h2 := hTp.dvd_orderOf (g := ⟨s ^ 2, hs2T⟩) (by
      intro h
      exact hs2ne (by simpa using congrArg Subtype.val h))
    rw [Subgroup.orderOf_mk] at h2
    exact even_iff_two_dvd.mpr h2
  have hnormCg : ∀ v : G, v * s ^ 2 = s ^ 2 * v → v ∈ Subgroup.normalizer (Cg : Set G) :=
    fun v hv => mem_normalizer_conj_of_commute hL hs2even (Subgroup.mem_inf.mp hs2T).2 hv
  have hRT : ∀ c ∈ R, c ∈ T → c = 1 := by
    intro c hcR hcT
    have hgC : g ∉ Subgroup.normalizer (Subgroup.centralizer (L : Set G) : Set G) := by
      rwa [hNC]
    have hc : c ∈ Subgroup.centralizer (L : Set G) ⊓ Cg := Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_inf.mp hcR).2, (Subgroup.mem_inf.mp hcT).2⟩
    have hdvd := Subgroup.orderOf_dvd_natCard _ hc
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hRp) ⟨c, hcR⟩
    rw [Subgroup.orderOf_mk] at hk
    by_contra hne
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hne (orderOf_eq_one_iff.mp (by simpa using hk))
    have h2 : 2 ∣ orderOf c := hk ▸ dvd_pow_self 2 hk0
    exact (Nat.not_even_iff_odd.mpr (hodd g hgC)) (even_iff_two_dvd.mpr (h2.trans hdvd))
  have hsq : ∀ v ∈ R, v * s ^ 2 = s ^ 2 * v → v * s = s * v := by
    intro v hv hv2
    have hvY : v ∈ Subgroup.normalizer (Y : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_inf.mp hv).1
    have hvT : v ∈ Subgroup.normalizer (T : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨hvY, hnormCg v hv2⟩
    have h1 : v * s * v⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hvT s).mp hsT
    have hcT : v * s * v⁻¹ * s⁻¹ ∈ T := Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hsT)
    have hcR : v * s * v⁻¹ * s⁻¹ ∈ R := by
      have h2 : s * v⁻¹ * s⁻¹ ∈ R :=
        (Subgroup.mem_normalizer_iff.mp hsR v⁻¹).mp (Subgroup.inv_mem _ hv)
      have h3 := Subgroup.mul_mem _ hv h2
      simpa [mul_assoc] using h3
    have h4 := hRT _ hcR hcT
    calc v * s = v * s * v⁻¹ * s⁻¹ * (s * v) := by group
      _ = s * v := by rw [h4, one_mul]
  obtain ⟨z, hzR, hz2, hinv⟩ :
      ∃ z ∈ R, z * z = 1 ∧ ∀ w ∈ R, w * w = 1 → w = 1 ∨ w = z := by
    by_cases h : ∃ z ∈ R, orderOf z = 2
    · obtain ⟨z, hzR, hz⟩ := h
      refine ⟨z, hzR, by rw [← sq, ← hz, pow_orderOf_eq_one], fun w hw hww => ?_⟩
      by_cases hw1 : w = 1
      · exact Or.inl hw1
      · exact Or.inr (eq_of_orderOf_eq_two_of_isCyclic hRcyc hw hzR
          (orderOf_eq_prime (by rw [sq, hww]) hw1) hz)
    · refine ⟨1, Subgroup.one_mem _, mul_one 1, fun w hw hww => Or.inl ?_⟩
      by_contra hw1
      exact h ⟨w, hw, orderOf_eq_prime (by rw [sq, hww]) hw1⟩
  have hzs : z * s = s * z := by
    have hconj : s * z * s⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.mp hsR z).mp hzR
    have hsq1 : (s * z * s⁻¹) * (s * z * s⁻¹) = 1 := by
      calc (s * z * s⁻¹) * (s * z * s⁻¹) = s * (z * z) * s⁻¹ := by group
        _ = 1 := by rw [hz2, mul_one, mul_inv_cancel]
    rcases hinv _ hconj hsq1 with h | h
    · have hz1 : z = 1 := by
        calc z = s⁻¹ * (s * z * s⁻¹) * s := by group
          _ = 1 := by rw [h, mul_one, inv_mul_cancel]
      rw [hz1, one_mul, mul_one]
    · calc z * s = s * z * s⁻¹ * s := by rw [h]
        _ = s * z := by group
  have hall := commute_of_pow_two_pow_commute hRp hRab hsR hzs hz2 hinv hsq
  refine ⟨fun v hv => ?_, fun v hv => hnormCg v ((Commute.pow_right (hall v hv) 2).eq)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  obtain ⟨k, rfl⟩ := hTzp x hx
  have hc : Commute s v := (hall v hv).symm
  exact (hc.zpow_left k).eq

theorem exists_full_conj_centralized [Finite G] {L : Subgroup G}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (S : Sylow 2 (Subgroup.centralizer (L : Set G))) (hS : IsCyclic S) {g : G}
    (hg : g ∉ Subgroup.normalizer (L : Set G)) {P : Subgroup G}
    (hPg : P ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g).toMonoidHom)
    (hPN : P ≤ Subgroup.normalizer (L : Set G)) (hP : IsPGroup 2 P) (hP4 : 4 ≤ Nat.card P) :
    ∃ g' : G, g' ∉ Subgroup.normalizer (L : Set G) ∧ ∃ R T : Subgroup G,
      R ≤ Subgroup.centralizer (L : Set G) ∧ IsPGroup 2 R ∧ Nat.card R = Nat.card S ∧
      T ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g').toMonoidHom ∧
      T ≤ Subgroup.normalizer (L : Set G) ∧ IsPGroup 2 T ∧ Nat.card T = Nat.card S ∧
      R ≤ Subgroup.centralizer (T : Set G) := by
  classical
  have hL' := hL
  obtain ⟨-, -, -, hNC, -⟩ := hL'
  set N := Subgroup.normalizer (L : Set G) with hNdef
  have hCN : (Subgroup.centralizer (L : Set G)) ≤ N := hNC ▸ Subgroup.le_normalizer
  have hNC' : N ≤ Subgroup.normalizer ((Subgroup.centralizer (L : Set G)) : Set G) := hNC.ge
  set S₀ : Subgroup G := (S : Subgroup (Subgroup.centralizer (L : Set G))).map
    (Subgroup.centralizer (L : Set G)).subtype with hS₀def
  have hS₀C : S₀ ≤ (Subgroup.centralizer (L : Set G)) := Subgroup.map_subtype_le _
  have hS₀ : IsPGroup 2 S₀ := S.isPGroup'.map _
  have hS₀card : Nat.card S₀ = Nat.card S :=
    Subgroup.card_map_of_injective
      (Subgroup.subtype_injective (Subgroup.centralizer (L : Set G)))
  obtain ⟨Y₁, hPY₁, hY₁N, hY₁, hY₁C⟩ :=
    exists_twoSubgroup_inf_card_ge hCN hNC' hS₀C hS₀ hPN hP
  have hT₁ : 4 ≤ Nat.card (Y₁ ⊓ (Subgroup.centralizer (L : Set G)).map
      (MulAut.conj g).toMonoidHom : Subgroup G) :=
    hP4.trans (Subgroup.card_le_of_le (le_inf hPY₁ hPg))
  obtain ⟨-, hR₁norm⟩ := inf_centralizer_le_centralizer hL S hS hg hY₁N hY₁ hT₁
  have hR₁card : Nat.card (Y₁ ⊓ (Subgroup.centralizer (L : Set G)) : Subgroup G) =
      Nat.card S := by
    refine le_antisymm (isCyclic_and_card_le_of_le S hS inf_le_right
      (hY₁.to_le inf_le_left)).2 ?_
    rw [← hS₀card]
    exact hY₁C
  set P₂ := (Y₁ ⊓ (Subgroup.centralizer (L : Set G))).map (MulAut.conj g⁻¹).toMonoidHom
    with hP₂def
  have hP₂g : P₂ ≤ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom :=
    Subgroup.map_mono inf_le_right
  have hP₂N : P₂ ≤ N := by
    rintro _ ⟨v, hv, rfl⟩
    have h := conj_inv_mem_normalizer_of_mem (hR₁norm hv)
    rw [hNC] at h
    simpa [MulAut.conj_apply] using h
  have hP₂ : IsPGroup 2 P₂ := (hY₁.to_le inf_le_left).map _
  have hP₂card : Nat.card P₂ = Nat.card S := (card_map_conj _ g⁻¹).trans hR₁card
  have hg' : g⁻¹ ∉ N := fun h => hg (by simpa using Subgroup.inv_mem _ h)
  obtain ⟨Y₂, hPY₂, hY₂N, hY₂, hY₂C⟩ :=
    exists_twoSubgroup_inf_card_ge hCN hNC' hS₀C hS₀ hP₂N hP₂
  have hT₂ge : Nat.card S ≤ Nat.card (Y₂ ⊓ (Subgroup.centralizer (L : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) := by
    rw [← hP₂card]
    exact Subgroup.card_le_of_le (le_inf hPY₂ hP₂g)
  have hT₂p : IsPGroup 2 (Y₂ ⊓ (Subgroup.centralizer (L : Set G)).map
      (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
    hY₂.to_le inf_le_left
  have hS4 : 4 ≤ Nat.card S := hP4.trans (isCyclic_and_card_le_of_le_conj S hS hPg hP).2
  obtain ⟨hR₂cent, -⟩ := inf_centralizer_le_centralizer hL S hS hg' hY₂N hY₂ (hS4.trans hT₂ge)
  refine ⟨g⁻¹, hg', Y₂ ⊓ (Subgroup.centralizer (L : Set G)),
    Y₂ ⊓ (Subgroup.centralizer (L : Set G)).map (MulAut.conj g⁻¹).toMonoidHom, inf_le_right,
    hY₂.to_le inf_le_left, ?_, inf_le_right, inf_le_left.trans hY₂N, hT₂p,
    le_antisymm (isCyclic_and_card_le_of_le_conj S hS inf_le_right hT₂p).2 hT₂ge, hR₂cent⟩
  refine le_antisymm (isCyclic_and_card_le_of_le S hS inf_le_right (hY₂.to_le inf_le_left)).2 ?_
  rw [← hS₀card]
  exact hY₂C

theorem normal_of_forall_odd_inf {X : Type} [Group X] [Finite X] {L : Subgroup X}
    (hL : CFSG.Assembly.ComponentType.IsStandardSubgroup L)
    (hO : CFSG.Assembly.oddCore X = ⊥) (S : Sylow 2 (Subgroup.centralizer (L : Set X)))
    (hS : IsCyclic S)
    (hodd : ∀ g : X, g ∉ Subgroup.normalizer (L : Set X) →
      Odd (Nat.card ((Subgroup.centralizer (L : Set X)).map (MulAut.conj g).toMonoidHom ⊓
        Subgroup.normalizer (L : Set X) : Subgroup X))) :
    L.Normal := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL' := hL
  obtain ⟨-, heven, -, hNC, -⟩ := hL'
  set N := Subgroup.normalizer (L : Set X) with hNdef
  obtain ⟨⟨z, hzC⟩, hz⟩ := exists_prime_orderOf_dvd_card' (G := (Subgroup.centralizer (L : Set X)))
    2 (even_iff_two_dvd.mp heven)
  rw [Subgroup.orderOf_mk] at hz
  have hcyc : ∀ P : Subgroup X, P ≤ (Subgroup.centralizer (L : Set X)) → IsPGroup 2 P →
      IsCyclic P :=
    fun P hPC hP => (isCyclic_and_card_le_of_le S hS hPC hP).1
  have hz1 : z ≠ 1 := by
    rintro rfl
    simp at hz
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hCz := (standard_involution_centralizer_normality hL hzC hz).1
  have hisol : ∀ h : X, (h * z * h⁻¹) * z = z * (h * z * h⁻¹) → h * z * h⁻¹ = z := by
    intro h hcomm
    have hyN : h * z * h⁻¹ ∈ N := hCz (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    have hyCh : h * z * h⁻¹ ∈ (Subgroup.centralizer (L : Set X)).map (MulAut.conj h).toMonoidHom :=
      conj_mem_conj hzC
    have hyord : orderOf (h * z * h⁻¹) = 2 := by
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, hz]
    have hhN : h ∈ N := by
      by_contra hhN
      have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hyCh, hyN⟩)
      rw [hyord] at hdvd
      exact (Nat.not_even_iff_odd.mpr (hodd h hhN)) (even_iff_two_dvd.mpr hdvd)
    have hyC : h * z * h⁻¹ ∈ (Subgroup.centralizer (L : Set X)) :=
      (Subgroup.mem_normalizer_iff.mp (hNC ▸ hhN) z).mp hzC
    exact eq_of_commute_of_orderOf_eq_two hcyc hyC hzC hyord hz hcomm
  let _ : Fintype X := Fintype.ofFinite X
  obtain ⟨N', hN'n, hN'odd, hN'⟩ := CFSG.ZStar.glauberman_zStar X z hz1 hzz hisol
  have hN'le : N' ≤ CFSG.Assembly.oddCore X := le_sSup ⟨hN'n, hN'odd⟩
  rw [hO, le_bot_iff] at hN'le
  have hcen : ∀ h : X, h ∈ N := by
    intro h
    have h1 := hN' h
    rw [hN'le, Subgroup.mem_bot, mul_inv_eq_one] at h1
    refine hCz (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    calc h * z = h * z * h⁻¹ * h := by group
      _ = z * h := by rw [h1]
  exact Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun h _ => hcen h)

end CFSG.LocalAnalysis.ComponentInitial.Finkelstein1977
