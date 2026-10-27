module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltComp
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltRank
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264AltUtil
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Orbit
public import CFSG.LocalAnalysis.GLTheoremA.S6.AltAux

public section

open CFSG.Open Equiv Subgroup

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Core

open CFSG.LocalAnalysis.GLTheoremA.KD264Inner CFSG.LocalAnalysis.GLTheoremA.KD264Comp
  CFSG.LocalAnalysis.GLTheoremA.KD264Util CFSG.LocalAnalysis.GLTheoremA.KD264Rank
  CFSG.LocalAnalysis.GLTheoremA

variable {Y : Type} [Group Y] [Finite Y]

theorem indep_pow {p : ℕ} (hp : p.Prime) {α : Type*} [Fintype α] [DecidableEq α]
    (x y : Perm α) (A B : Finset α) (hx : x ^ p = 1) (hy : y ^ p = 1)
    (hA : ∀ j : ℕ, ¬ p ∣ j → ∀ t, (x ^ j) t ≠ t ↔ t ∈ A)
    (hB : ∀ j : ℕ, ¬ p ∣ j → ∀ t, (y ^ j) t ≠ t ↔ t ∈ B)
    (hAB : Disjoint A B) (hAne : A.Nonempty) (hBne : B.Nonempty) (i j : ℕ)
    (h : x ^ i = y ^ j) : p ∣ i ∧ p ∣ j := by
  have hfixA : ∀ i : ℕ, ∀ t, t ∉ A → (x ^ i) t = t := by
    intro i t ht
    by_cases hi : p ∣ i
    · obtain ⟨c, rfl⟩ := hi
      rw [pow_mul, hx, one_pow, Equiv.Perm.one_apply]
    · by_contra h'
      exact ht ((hA i hi t).1 (fun h2 => h' h2))
  have hfixB : ∀ j : ℕ, ∀ t, t ∉ B → (y ^ j) t = t := by
    intro j t ht
    by_cases hj : p ∣ j
    · obtain ⟨c, rfl⟩ := hj
      rw [pow_mul, hy, one_pow, Equiv.Perm.one_apply]
    · by_contra h'
      exact ht ((hB j hj t).1 (fun h2 => h' h2))
  have hj : p ∣ j := by
    by_contra hj
    obtain ⟨t, ht⟩ := hBne
    have h1 : (y ^ j) t ≠ t := (hB j hj t).2 ht
    have h2 : (y ^ j) t = t := by
      rw [← h]
      exact hfixA i t (fun htA => Finset.disjoint_left.1 hAB htA ht)
    exact h1 h2
  refine ⟨?_, hj⟩
  by_contra hi
  obtain ⟨t, ht⟩ := hAne
  have h1 : (x ^ i) t ≠ t := (hA i hi t).2 ht
  have h2 : (x ^ i) t = t := by
    rw [h]
    exact hfixB j t (fun htB => Finset.disjoint_left.1 hAB ht htB)
  exact h1 h2

theorem support_mul_eq {α : Type*} [Fintype α] [DecidableEq α] (x y : Perm α) (A B : Finset α)
    (hA : ∀ t, x t ≠ t ↔ t ∈ A) (hB : ∀ t, y t ≠ t ↔ t ∈ B) (hAB : Disjoint A B) :
    (x * y).support = A ∪ B := by
  ext t
  rw [Equiv.Perm.mem_support, Finset.mem_union]
  constructor
  · intro ht
    have h1 := support_mul_subset' x y (Equiv.Perm.mem_support.2 ht)
    rw [Finset.mem_union, Equiv.Perm.mem_support, Equiv.Perm.mem_support] at h1
    rcases h1 with h1 | h1
    · exact Or.inl ((hA t).1 h1)
    · exact Or.inr ((hB t).1 h1)
  · rintro (htA | htB)
    · have hyt : y t = t := by
        by_contra h'
        exact Finset.disjoint_left.1 hAB htA ((hB t).1 h')
      rw [Equiv.Perm.mul_apply, hyt]
      exact (hA t).2 htA
    · have hyB : y t ∈ B := maps_into_of_fix_outside y B (fun s hs => by
        by_contra h'
        exact hs ((hB s).1 h')) htB ((hB t).2 htB)
      have hxyt : x (y t) = y t := by
        by_contra h'
        exact Finset.disjoint_left.1 hAB ((hA _).1 h') hyB
      rw [Equiv.Perm.mul_apply, hxyt]
      exact (hB t).2 htB

theorem psiImage_comap {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n)
    (K : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n)) (B : Subgroup Y)
    (hB : ∀ b ∈ B, b ^ p = 1) (Q : Subgroup (alternatingGroup (Fin n)))
    (hQ : Q ≤ (psiHom K hK e hp hp2 hn B hB).range) :
    psiImage K hK e hp hp2 hn B hB ((Q.comap (psiHom K hK e hp hp2 hn B hB)).map B.subtype) = Q := by
  classical
  ext g
  constructor
  · intro hg
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
    have hwE : (w : Y) ∈ (Q.comap (psiHom K hK e hp hp2 hn B hB)).map B.subtype :=
      Subgroup.mem_subgroupOf.1 hw
    obtain ⟨u, hu, huw⟩ := Subgroup.mem_map.1 hwE
    have huw' : u = w := Subtype.ext huw
    rw [← huw']
    exact Subgroup.mem_comap.1 hu
  · intro hg
    obtain ⟨w, hw⟩ := (MonoidHom.mem_range).1 (hQ hg)
    refine Subgroup.mem_map.2 ⟨w, Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨w, ?_, rfl⟩), hw⟩
    exact Subgroup.mem_comap.2 (by rw [hw]; exact hg)

theorem alt_core {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {n : ℕ} (hn : 5 ≤ n) (hpn : p ≤ n)
    (K B : Subgroup Y) (hK : K.Normal) (e : K ≃* alternatingGroup (Fin n))
    (hZ : Subgroup.center ↥K = ⊥) (hB : CFSG.Open.IsElemAbelian p B)
    (hBcard : p ^ 4 ≤ Nat.card B) (hmax : IsMaxRankIn p B ⊤)
    (hC : B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥)
    (hp3 : p = 3 → n ≠ 6 ∧ n ≠ 7 ∧ n ≠ 9 ∧ n ≠ 10) :
    ∃ E : Subgroup Y, E ≤ B ∧ CFSG.Open.IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥ := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3' : 3 ≤ p := by
    have := hp.two_le
    omega
  have hB' : ∀ b ∈ B, b ^ p = 1 := fun b hb => hB.2 b hb
  set ψ := psiHom K hK e hp hp2 hn B hB' with hψ
  set C : Subgroup Y := B ⊓ Subgroup.centralizer (K : Set Y) with hCdef
  set P : Subgroup (alternatingGroup (Fin n)) := ψ.range with hPdef
  have hPel : CFSG.Open.IsElemAbelian p P :=
    isElemAbelian_range_of_hom hB.1 (fun g => Subtype.ext (hB.2 g.1 g.2)) ψ
  have hBp : IsPGroup p B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g.1 g.2)⟩
  obtain ⟨m, hm⟩ := hBp.exists_card_eq
  have hCle : C ≤ B := inf_le_left
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow hp).1 (hm ▸ Subgroup.card_dvd_of_le hCle)
  have hkerC : Nat.card C = Nat.card ψ.ker := card_inf_centralizer_eq_ker hp hp2 hn K hK e B hB
  have hsplit : Nat.card ψ.ker * Nat.card P = Nat.card B := Subgroup.card_ker_mul_card_range ψ
  obtain ⟨E₀, -, hE₀, hE₀card, -⟩ := CFSG.LocalAnalysis.GLTheoremA.exists_elemAbelian_blocks hp hp2 hpn
  have hrank : Nat.card E₀ ≤ Nat.card P :=
    card_le_range_of_elemAbelian hp hp2 hn K hK hZ e B hB hmax E₀ hE₀
  set P' : Subgroup (Perm (Fin n)) := P.map (alternatingGroup (Fin n)).subtype with hP'def
  have hP'el : CFSG.Open.IsElemAbelian p P' := isElemAbelian_map_of_hom hPel _
  have hP'card : Nat.card P' = Nat.card P :=
    Subgroup.card_map_of_injective (Subgroup.subtype_injective _)
  obtain ⟨hPk, horb⟩ := CFSG.LocalAnalysis.GLTheoremA.KD264Orbit.orbit_pCycles hp hp3' P' hP'el
    (by rw [hP'card, ← hE₀card]; exact hrank)
  have hPkP : Nat.card P = p ^ (n / p) := hP'card ▸ hPk
  set k := n / p with hk
  have hmc : m = c + k := by
    have h1 : p ^ m = p ^ c * p ^ k := by
      rw [← hm, ← hsplit, ← hkerC, hc, hPkP]
    exact Nat.pow_right_injective hp.two_le (h1.trans (pow_add p c k).symm)
  have hm4 : 4 ≤ m := by
    have h1 : p ^ 4 ≤ p ^ m := hm ▸ hBcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1
  have hc1 : 1 ≤ c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exfalso
      have hCtriv : Nat.card C = 1 := by rw [hc, h0, pow_zero]
      exact hC (Subgroup.eq_bot_of_card_eq C hCtriv)
    · exact h0
  have h2pk : 2 * p ≤ n ∨ k < 2 := by
    by_cases hk2 : 2 ≤ k
    · left
      have : 2 ≤ n / p := hk2
      exact (Nat.le_div_iff_mul_le hp.pos).1 this
    · right
      omega
  have hp_cases : p = 3 ∨ 5 ≤ p := by
    have h4 : p ≠ 4 := by
      rintro rfl
      norm_num at hp
    omega
  rcases (show 3 ≤ c ∨ c = 2 ∨ c = 1 by omega) with hc3 | hc2 | hc1'
  ·
    obtain ⟨E, hEcard, -, hEC⟩ := Sylow.exists_subgroup_card_pow_prime_le_le hp
      (H := (⊥ : Subgroup Y)) (L := C) (n := 3) (by simp)
      (by rw [hc]; exact pow_dvd_pow p hc3) bot_le
    have hEB : E ≤ B := hEC.trans hCle
    have hEel : CFSG.Open.IsElemAbelian p E := isElemAbelian_mono hB hEB
    have hpsiE : psiImage K hK e hp hp2 hn B hB' E = ⊥ := by
      rw [eq_bot_iff]
      rintro g hg
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hg
      have hwC : (w : Y) ∈ C := hEC (Subgroup.mem_subgroupOf.1 hw)
      have hwK : (w : Y) ∈ Subgroup.centralizer (K : Set Y) := hwC.2
      have h1 : ψ w = 1 := (psiHom_eq_one_iff K hK e hp hp2 hn B hB' w).2 hwK
      rw [h1, Subgroup.mem_bot]
    refine ⟨E, hEB, hEel, hEcard, ?_⟩
    have h1 : (1 : alternatingGroup (Fin n)) ∈ psiImage K hK e hp hp2 hn B hB' E :=
      Subgroup.one_mem _
    refine glaPLayer_ne_bot_of_psi K hK e hp hp2 hn B hB' E hEB 1 h1 (fun g hg => ?_) ?_ ?_
    · rw [hpsiE, Subgroup.mem_bot] at hg
      simp [hg]
    · simpa using hn
    · simpa using hpn
  ·
    have hk2 : 2 ≤ k := by omega
    have h2p : 2 * p ≤ n := by
      rcases h2pk with h | h
      · exact h
      · omega
    obtain ⟨a, b, ha, -, A, B', hAc, -, hAB, hA, -⟩ := horb hk2
    obtain ⟨x, hxP, hxa⟩ := Subgroup.mem_map.1 ha
    have hxval : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = a := hxa
    have hxp : x ^ p = 1 := hPel.2 x hxP
    have hA1 : ∀ t, a t ≠ t ↔ t ∈ A := fun t => by
      simpa using hA 1 (Nat.Prime.not_dvd_one hp) t
    have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
    have hsuppx : (x : Perm (Fin n)).support = A := by
      ext t
      rw [Equiv.Perm.mem_support, hxval]
      exact hA1 t
    have hx1 : x ≠ 1 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hAne
      have ha1 : a = 1 := by rw [← hxval]; rfl
      exact (hA1 t).2 ht (by rw [ha1]; rfl)
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hQP : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
    have hQcard : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, hxord]
    have hEcard : Nat.card (((Subgroup.zpowers x).comap ψ).map B.subtype : Subgroup Y) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        card_comap_eq_mul ψ _ hQP, hQcard, ← hkerC, hc, hc2]
      ring
    have hEB : (((Subgroup.zpowers x).comap ψ).map B.subtype : Subgroup Y) ≤ B :=
      Subgroup.map_subtype_le _
    have hEel := isElemAbelian_mono hB hEB
    have hpsiE := psiImage_comap hp hp2 hn K hK e B hB' (Subgroup.zpowers x) hQP
    have hτ : x ∈ psiImage K hK e hp hp2 hn B hB' (((Subgroup.zpowers x).comap ψ).map B.subtype : Subgroup Y) := by
      rw [hpsiE]
      exact Subgroup.mem_zpowers x
    have hQle : Subgroup.zpowers x ≤ altOn (x : Perm (Fin n)).support :=
      Subgroup.zpowers_le.2 (mem_altOn_iff.2 subset_rfl)
    have hsupp : ∀ g ∈ psiImage K hK e hp hp2 hn B hB' (((Subgroup.zpowers x).comap ψ).map B.subtype : Subgroup Y),
        (g : Perm (Fin n)).support ⊆ (x : Perm (Fin n)).support := by
      intro g hg
      rw [hpsiE] at hg
      exact mem_altOn_iff.1 (hQle hg)
    have hcardx : (x : Perm (Fin n)).support.card = p := by rw [hsuppx, hAc]
    refine ⟨_, hEB, hEel, hEcard, ?_⟩
    refine glaPLayer_ne_bot_of_psi K hK e hp hp2 hn B hB' _ hEB x hτ hsupp ?_ ?_
    · rw [hcardx]
      rcases hp_cases with h3 | h5
      · obtain ⟨h6, h7, -, -⟩ := hp3 h3
        omega
      · omega
    · rw [hcardx]
      omega
  ·
    have hk3 : 3 ≤ k := by omega
    have h3p : 3 * p ≤ n := (Nat.le_div_iff_mul_le hp.pos).1 hk3
    obtain ⟨a, b, ha, hb, A, B', hAc, hBc, hAB, hA, hB'o⟩ := horb (by omega)
    obtain ⟨x, hxP, hxa⟩ := Subgroup.mem_map.1 ha
    obtain ⟨y, hyP, hyb⟩ := Subgroup.mem_map.1 hb
    have hxval : ((x : alternatingGroup (Fin n)) : Perm (Fin n)) = a := hxa
    have hyval : ((y : alternatingGroup (Fin n)) : Perm (Fin n)) = b := hyb
    have hap : a ^ p = 1 := hP'el.2 a ha
    have hbp : b ^ p = 1 := hP'el.2 b hb
    have hA1 : ∀ t, a t ≠ t ↔ t ∈ A := fun t => by
      simpa using hA 1 (Nat.Prime.not_dvd_one hp) t
    have hB1 : ∀ t, b t ≠ t ↔ t ∈ B' := fun t => by
      simpa using hB'o 1 (Nat.Prime.not_dvd_one hp) t
    have hAne : A.Nonempty := Finset.card_pos.1 (by omega)
    have hBne : B'.Nonempty := Finset.card_pos.1 (by omega)
    have hxp : x ^ p = 1 := hPel.2 x hxP
    have hyp : y ^ p = 1 := hPel.2 y hyP
    have hx1 : x ≠ 1 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hAne
      have ha1 : a = 1 := by rw [← hxval]; rfl
      exact (hA1 t).2 ht (by rw [ha1]; rfl)
    have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
    have hyord : orderOf y = p := orderOf_eq_prime hyp (by
      rintro rfl
      obtain ⟨t, ht⟩ := hBne
      have hb1 : b = 1 := by rw [← hyval]; rfl
      exact (hB1 t).2 ht (by rw [hb1]; rfl))
    have hcommP : ∀ u ∈ P, ∀ v ∈ P, u * v = v * u := fun u hu v hv => by
      have := hPel.1.is_comm.comm (⟨u, hu⟩ : P) ⟨v, hv⟩
      exact congrArg Subtype.val this
    have hindep : ∀ i j : ℕ, a ^ i = b ^ j → p ∣ i ∧ p ∣ j :=
      fun i j h => indep_pow hp a b A B' hap hbp hA hB'o hAB hAne hBne i j h
    have hinf : Subgroup.zpowers x ⊓ Subgroup.zpowers y = ⊥ := by
      rw [eq_bot_iff]
      intro u hu
      rw [Subgroup.mem_inf] at hu
      obtain ⟨hu1, hu2⟩ := hu
      rw [mem_zpowers_iff_mem_range_orderOf] at hu1 hu2
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hu1
      obtain ⟨j, -, hji⟩ := Finset.mem_image.1 hu2
      have hperm : a ^ i = b ^ j := by
        rw [← hxval, ← hyval, ← Subgroup.coe_pow, ← Subgroup.coe_pow, hji]
      obtain ⟨hi, -⟩ := hindep i j hperm
      obtain ⟨c', hc'⟩ := hi
      rw [Subgroup.mem_bot, hc', pow_mul, hxp, one_pow]
    have hyN' : y ∈ Subgroup.normalizer
        ((Subgroup.zpowers x : Subgroup (alternatingGroup (Fin n))) :
          Set (alternatingGroup (Fin n))) := by
      have hQP' : Subgroup.zpowers x ≤ P := Subgroup.zpowers_le.2 hxP
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        have hkey : y * h * y⁻¹ = h := by
          rw [hcommP y hyP h (hQP' hh)]
          group
        rw [hkey]
        exact hh
      · intro hh
        have hP1 : y * h * y⁻¹ ∈ P := hQP' hh
        have hhP : h ∈ P := by
          have hh' : h = y⁻¹ * (y * h * y⁻¹) * y⁻¹⁻¹ := by group
          rw [hh']
          exact P.mul_mem (P.mul_mem (P.inv_mem hyP) hP1) (P.inv_mem (P.inv_mem hyP))
        have hkey : y * h * y⁻¹ = h := by
          rw [hcommP y hyP h hhP]
          group
        rw [← hkey]
        exact hh
    have hyN : Subgroup.zpowers y ≤ Subgroup.normalizer
        ((Subgroup.zpowers x : Subgroup (alternatingGroup (Fin n))) :
          Set (alternatingGroup (Fin n))) := Subgroup.zpowers_le.2 hyN'
    have hQP : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ P :=
      sup_le (Subgroup.zpowers_le.2 hxP) (Subgroup.zpowers_le.2 hyP)
    have hQcard : Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = p * p := by
      have h1 := card_sup_mul_card_inf_of_le_normalizer hyN
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers, hxord, hyord] at h1
      exact h1
    have hEcard : Nat.card (((((Subgroup.zpowers x ⊔ Subgroup.zpowers y)).comap ψ).map B.subtype :
        Subgroup Y)) = p ^ 3 := by
      rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _),
        card_comap_eq_mul ψ _ hQP, hQcard, ← hkerC, hc, hc1']
      ring
    have hEB : ((((Subgroup.zpowers x ⊔ Subgroup.zpowers y)).comap ψ).map B.subtype : Subgroup Y) ≤ B :=
      Subgroup.map_subtype_le _
    have hEel := isElemAbelian_mono hB hEB
    have hpsiE := psiImage_comap hp hp2 hn K hK e B hB' _ hQP
    have hτ : x * y ∈ psiImage K hK e hp hp2 hn B hB'
        ((((Subgroup.zpowers x ⊔ Subgroup.zpowers y)).comap ψ).map B.subtype : Subgroup Y) := by
      rw [hpsiE]
      exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
    have hxsupp : (x : Perm (Fin n)).support = A := by
      ext t
      rw [Equiv.Perm.mem_support, hxval]
      exact hA1 t
    have hysupp : (y : Perm (Fin n)).support = B' := by
      ext t
      rw [Equiv.Perm.mem_support, hyval]
      exact hB1 t
    have hτsupp : ((x * y : alternatingGroup (Fin n)) : Perm (Fin n)).support = A ∪ B' := by
      rw [Subgroup.coe_mul, hxval, hyval]
      exact support_mul_eq a b A B' hA1 hB1 hAB
    have hQle : Subgroup.zpowers x ⊔ Subgroup.zpowers y ≤ altOn (A ∪ B') :=
      sup_le (Subgroup.zpowers_le.2 (mem_altOn_iff.2 (by rw [hxsupp]; exact Finset.subset_union_left)))
        (Subgroup.zpowers_le.2 (mem_altOn_iff.2 (by rw [hysupp]; exact Finset.subset_union_right)))
    have hsupp : ∀ g ∈ psiImage K hK e hp hp2 hn B hB'
        ((((Subgroup.zpowers x ⊔ Subgroup.zpowers y)).comap ψ).map B.subtype : Subgroup Y),
        (g : Perm (Fin n)).support ⊆ ((x * y : alternatingGroup (Fin n)) : Perm (Fin n)).support := by
      intro g hg
      rw [hpsiE] at hg
      rw [hτsupp]
      exact mem_altOn_iff.1 (hQle hg)
    have hcard_union : ((x * y : alternatingGroup (Fin n)) : Perm (Fin n)).support.card = p + p := by
      rw [hτsupp, Finset.card_union_of_disjoint hAB, hAc, hBc]
    refine ⟨_, hEB, hEel, hEcard, ?_⟩
    refine glaPLayer_ne_bot_of_psi K hK e hp hp2 hn B hB' _ hEB (x * y) hτ hsupp ?_ ?_
    · rw [hcard_union]
      rcases hp_cases with h3 | h5
      · obtain ⟨-, -, h9, h10⟩ := hp3 h3
        omega
      · omega
    · rw [hcard_union]
      omega

end CFSG.LocalAnalysis.GLTheoremA.KD264Core
