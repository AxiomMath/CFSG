module

public import CFSG.ClassicalInvolution.Q3.TL3T37
public import CFSG.ClassicalInvolution.Q3.TL3T45
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael

public section

namespace CFSG.ClassicalInvolution.Q3.AE

open Wr Certificates.AE117 CFSG.ComponentClassification.PresentationLocal

variable {n : ℕ}

abbrev CMI (n : ℕ) := CarmichaelIndex n

theorem kk_d₂ : ∃ k ∈ kList, ∃ k' ∈ kStarList, k * k' = ofPerm d₂ := by decide +kernel

theorem inf_memBar_true_false (hn : 5 ≤ n) {α : Finset (Fin n)} {h : α.card = 4} {x : AEQ n}
    (hx : x ∈ memBar α h true) (hx' : x ∈ memBar α h false) : x = 1 ∨ x = zBar α h := by
  obtain ⟨a, ha, rfl⟩ := hx
  obtain ⟨a', ha', he⟩ := hx'
  have haa : a' = a := mkQ_inj_of_supportedOn hn (ι := emb α h)
    (supportedOn_of_mem_memAt ha') (supportedOn_of_mem_memAt ha) he
  subst haa
  obtain ⟨k, hk, rfl⟩ := ha
  obtain ⟨k', hk', hkk⟩ := ha'
  have hkk' := embed_injective _ hkk
  subst hkk'
  rcases inf_kQ_kQStar k' hk hk' with h1 | h1
  · left
    rw [h1, map_one, map_one]
  · right
    rw [h1]
    rfl

@[expose] def rho013 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 1 3

theorem rho013_three : rho013 * rho013 * rho013 = 1 ∧ rho013 ≠ 1 := by decide

theorem conj_carmichael_memLC {i j : CMI n} (hij : i.1 ≠ j.1) (ι : Fin 4 ↪ Fin n)
    (h0 : ι 0 = ⟨0, by have := i.two_lt; omega⟩) (h1 : ι 1 = ⟨1, by have := i.two_lt; omega⟩)
    (h2 : ι 2 = i.1) (h3 : ι 3 = j.1) (b : Bool) {x : Wr n}
    (hx : x ∈ memLC (ι 0) (ι 1) (ι 2) (ι 3) b) :
    ofPerm (carmichaelPerm j) * x * (ofPerm (carmichaelPerm j))⁻¹ ∈
      memLC (ι 0) (ι 1) (ι 2) (ι 3) b := by
  have hi := i.2
  have hj := j.2
  have hσ : ∀ a, carmichaelPerm j (ι a) = ι (rho013 a) := by
    intro a
    fin_cases a
    · show carmichaelPerm j (ι 0) = ι 1
      rw [h0, h1, carmichaelPerm_apply, ite_eq_left rfl]
    · show carmichaelPerm j (ι 1) = ι 3
      rw [h1, h3, carmichaelPerm_apply, ite_eq_right (by simp), ite_eq_left (by simp)]
    · show carmichaelPerm j (ι 2) = ι 2
      rw [h2, carmichaelPerm_apply, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_right hij]
    · show carmichaelPerm j (ι 3) = ι 0
      rw [h3, h0, carmichaelPerm_apply, ite_eq_right (by omega), ite_eq_right (by omega),
        ite_eq_left rfl]
  rw [memLC_eq'] at hx ⊢
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hx
  rw [ofPerm_conj_embed hσ]
  refine List.mem_map.mpr ⟨_, ?_, rfl⟩
  have h3' := rho013_three
  cases b
  · exact three_cycle_kStarList rho013 h3'.1 h3'.2 a ha
  · exact three_cycle_kList rho013 h3'.1 h3'.2 a ha

theorem exists_memLC_mul_eq {i j : CMI n} (ι : Fin 4 ↪ Fin n)
    (h0 : ι 0 = ⟨0, by have := i.two_lt; omega⟩) (h1 : ι 1 = ⟨1, by have := i.two_lt; omega⟩)
    (h2 : ι 2 = i.1) (h3 : ι 3 = j.1) :
    ∃ a ∈ memLC (ι 0) (ι 1) (ι 2) (ι 3) true, ∃ a' ∈ memLC (ι 0) (ι 1) (ι 2) (ι 3) false,
      a * a' = ofPerm (carmichaelPerm i * carmichaelPerm j) := by
  obtain ⟨k, hk, k', hk', hkk⟩ := kk_d₂
  refine ⟨embed ι k, ?_, embed ι k', ?_, ?_⟩
  · rw [memLC_eq']
    exact List.mem_map.mpr ⟨k, hk, rfl⟩
  · rw [memLC_eq']
    exact List.mem_map.mpr ⟨k', hk', rfl⟩
  · rw [← map_mul, hkk, carmichaelPerm_mul]
    refine Wr.ext (funext fun x => ?_) ?_
    · show embedVec ι (0 : Fin 4 → ZMod 2) x = 0
      by_cases hx : x ∈ Set.range ι
      · obtain ⟨a, rfl⟩ := hx
        rw [embedVec_apply]
        rfl
      · exact embedVec_of_not_mem ι _ hx
    · show embedPerm ι d₂ = _
      rw [TL4.Mdl117.embedPerm_d₂, h0, h1, h2, h3]
      rfl

end CFSG.ClassicalInvolution.Q3.AE

namespace CFSG.ClassicalInvolution.Q3.TC.Thin

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ComponentClassification.PresentationLocal

section Section

variable {G : Type} [Group G]

theorem cube_eq_of_comm {l l' x : G} (hx : x ^ 3 = 1)
    (h1 : l' * (x⁻¹ * l * x) = (x⁻¹ * l * x) * l')
    (h2 : l' * (x * l * x⁻¹) = (x * l * x⁻¹) * l')
    (h3 : (x⁻¹ * l' * x) * (x * l * x⁻¹) = (x * l * x⁻¹) * (x⁻¹ * l' * x)) :
    (l * l' * x⁻¹) ^ 3 = (l * (x⁻¹ * l * x) * (x * l * x⁻¹)) *
      (l' * (x⁻¹ * l' * x) * (x * l' * x⁻¹)) := by
  have hxx : x * x = x⁻¹ := by
    have : x * x * x = 1 := by rw [← pow_three']; exact hx
    calc x * x = x * x * x * x⁻¹ := by group
      _ = x⁻¹ := by rw [this, one_mul]
  have e : (l * l' * x⁻¹) ^ 3 = (l * l') * (x⁻¹ * (l * l') * x) * (x * (l * l') * x⁻¹) := by
    calc (l * l' * x⁻¹) ^ 3 = (l * l') * x⁻¹ * (l * l') * x⁻¹ * (l * l') * x⁻¹ := by
          rw [pow_three]
          group
      _ = (l * l') * x⁻¹ * (l * l') * (x * x) * (l * l') * x⁻¹ := by rw [hxx]
      _ = (l * l') * (x⁻¹ * (l * l') * x) * (x * (l * l') * x⁻¹) := by group
  rw [e]
  calc l * l' * (x⁻¹ * (l * l') * x) * (x * (l * l') * x⁻¹)
      = l * (l' * (x⁻¹ * l * x)) * (x⁻¹ * l' * x) * (x * l * x⁻¹) * (x * l' * x⁻¹) := by group
    _ = l * ((x⁻¹ * l * x) * l') * (x⁻¹ * l' * x) * (x * l * x⁻¹) * (x * l' * x⁻¹) := by rw [h1]
    _ = l * (x⁻¹ * l * x) * l' * ((x⁻¹ * l' * x) * (x * l * x⁻¹)) * (x * l' * x⁻¹) := by group
    _ = l * (x⁻¹ * l * x) * l' * ((x * l * x⁻¹) * (x⁻¹ * l' * x)) * (x * l' * x⁻¹) := by rw [h3]
    _ = l * (x⁻¹ * l * x) * (l' * (x * l * x⁻¹)) * (x⁻¹ * l' * x) * (x * l' * x⁻¹) := by group
    _ = l * (x⁻¹ * l * x) * ((x * l * x⁻¹) * l') * (x⁻¹ * l' * x) * (x * l' * x⁻¹) := by rw [h2]
    _ = (l * (x⁻¹ * l * x) * (x * l * x⁻¹)) * (l' * (x⁻¹ * l' * x) * (x * l' * x⁻¹)) := by group

theorem AEIdent.exists_section [Finite G] {P : Set (Subgroup G)} {n : ℕ} (hn : 5 ≤ n) (I : AEIdent P n)
    (hk2 : IsPGroup 2 I.φ.ker) (h8 : ∀ L ∈ P, Nat.card L = 8)
    (hzL : ∀ L ∈ P, ∃ u, IsUniqueInvolution L u)
    (htw : ∀ L ∈ P, ∀ L' ∈ P, ∀ (α : Finset (Fin n)) (hα : α.card = 4),
      (L.subgroupOf (pSpan P)).map I.φ = memBar α hα true →
      (L'.subgroupOf (pSpan P)).map I.φ = memBar α hα false →
      (∀ a ∈ L, ∀ b ∈ L', a * b = b * a) ∧
        ∀ u u', IsUniqueInvolution L u → IsUniqueInvolution L' u' → u = u')
    (hdet : ∀ L ∈ P, ∀ L' ∈ P,
      (L.subgroupOf (pSpan P)).map I.φ = (L'.subgroupOf (pSpan P)).map I.φ → L = L')
    (hinv : ∀ L ∈ P, ∀ x ∈ pSpan P, conjSub x L ∈ P) :
    ∃ s : alternatingGroup (Fin n) →* ↥(pSpan P),
      ∀ σ : alternatingGroup (Fin n), I.φ (s σ) = mkQ n (ofPerm (σ : Equiv.Perm (Fin n))) := by
  classical
  have hn3 : 3 ≤ n := by omega
  have hlift : ∀ k : CarmichaelIndex n, ∃ x : ↥(pSpan P),
      I.φ x = mkQ n (ofPerm (carmichaelPerm k)) ∧ x ^ 3 = 1 := by
    intro k
    have hmem : mkQ n (ofPerm (carmichaelPerm k)) ∈ I.φ.range := by
      rw [I.range_eq]
      exact mem_aeModel_ofPerm (carmichaelPerm_mem k)
    obtain ⟨e, he⟩ := hmem
    have hc3 : carmichaelPerm k ^ 3 = 1 := by
      rw [← (carmichaelPerm_isThreeCycle k).orderOf]
      exact pow_orderOf_eq_one _
    have h3 : e ^ 3 ∈ I.φ.ker := by
      rw [MonoidHom.mem_ker, map_pow, he, ← map_pow, ofPerm_pow, hc3, ofPerm_one, map_one]
    obtain ⟨t, ht⟩ := hk2 ⟨e ^ 3, h3⟩
    have ht' : e ^ (3 * 2 ^ t) = 1 := by
      have := congrArg Subtype.val ht
      rw [Subgroup.coe_pow, Subgroup.coe_one] at this
      rw [pow_mul]
      exact this
    have h4 : 4 ^ t % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    refine ⟨e ^ (4 ^ t), ?_, ?_⟩
    · rw [map_pow, he, ← map_pow, ofPerm_pow, ← Nat.div_add_mod (4 ^ t) 3, h4, pow_add,
        pow_mul, hc3, one_pow, one_mul, pow_one]
    · rw [← pow_mul, show 4 ^ t * 3 = (3 * 2 ^ t) * 2 ^ t by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow]; ring, pow_mul, ht', one_pow]
  choose x hxI hx3 using hlift
  have huniq : ∀ (k : CarmichaelIndex n) (v : ↥(pSpan P)),
      I.φ v = mkQ n (ofPerm (carmichaelPerm k)) → v ^ 3 = 1 → v = x k := fun k v hv hv3 =>
    I.eq_of_map_eq_of_pow hk2 (a := 1) (by simpa using hv3) (by simpa using hx3 k)
      (hv.trans (hxI k).symm)
  have hrel : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    have hi2 := i.2
    have hj2 := j.2
    have hij' : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
    have hi0 : (i.1 : ℕ) ≠ 0 := by omega
    have hi1 : (i.1 : ℕ) ≠ 1 := by omega
    have hj0 : (j.1 : ℕ) ≠ 0 := by omega
    have hj1 : (j.1 : ℕ) ≠ 1 := by omega
    set f : Fin 4 → Fin n := ![⟨0, by omega⟩, ⟨1, by omega⟩, i.1, j.1] with hfdef
    have hf : Function.Injective f := by
      intro a b hab
      have hv := congrArg Fin.val hab
      fin_cases a <;> fin_cases b <;> simp [hfdef] at hv ⊢ <;> omega
    set ι : Fin 4 ↪ Fin n := ⟨f, hf⟩ with hι
    set α : Finset (Fin n) := Finset.univ.map ι with hαdef
    have hα : α.card = 4 := by rw [hαdef, Finset.card_map, Finset.card_univ, Fintype.card_fin]
    have hr : Set.range ι = (α : Set (Fin n)) := by
      rw [hαdef, Finset.coe_map, Finset.coe_univ, Set.image_univ]
    obtain ⟨L, hL, hLl⟩ := I.label_surj α hα true
    obtain ⟨L', hL', hL'l⟩ := I.label_surj α hα false
    obtain ⟨hcomm, hzz⟩ := htw L hL L' hL' α hα hLl hL'l
    obtain ⟨u, hu⟩ := hzL L hL
    obtain ⟨u', hu'⟩ := hzL L' hL'
    have huu : u = u' := hzz u u' hu hu'
    obtain ⟨b₁, hb₁⟩ := exists_memBar_eq_memLC ι α hα hr true
    obtain ⟨b₂, hb₂⟩ := exists_memBar_eq_memLC ι α hα hr false
    have hb12 : b₁ ≠ b₂ := fun h => memBar_true_ne_false hn α hα (by ext y; rw [hb₁, hb₂, h])
    obtain ⟨a, ha, a', ha', haa⟩ := exists_memLC_mul_eq (i := i) (j := j) ι rfl rfl rfl rfl
    have hcommW : a * a' = a' * a := by
      rw [memLC_eq'] at ha ha'
      obtain ⟨k, hk, rfl⟩ := List.mem_map.mp ha
      obtain ⟨k', hk', rfl⟩ := List.mem_map.mp ha'
      exact comm_memK_memKStar ι _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩
    have hprod : ∃ y ∈ memBar α hα true, ∃ y' ∈ memBar α hα false,
        y * y' = mkQ n (ofPerm (carmichaelPerm i * carmichaelPerm j)) := by
      cases b₁ <;> cases b₂
      · exact absurd rfl hb12
      · refine ⟨mkQ n a', (hb₁ _).mpr ⟨a', ha', rfl⟩, mkQ n a, (hb₂ _).mpr ⟨a, ha, rfl⟩, ?_⟩
        rw [← map_mul, ← hcommW, haa]
      · refine ⟨mkQ n a, (hb₁ _).mpr ⟨a, ha, rfl⟩, mkQ n a', (hb₂ _).mpr ⟨a', ha', rfl⟩, ?_⟩
        rw [← map_mul, haa]
      · exact absurd rfl hb12
    obtain ⟨y, hy, y', hy', hyy⟩ := hprod
    rw [← hLl] at hy
    rw [← hL'l] at hy'
    obtain ⟨⟨l, hlP⟩, hlL, rfl⟩ := hy
    obtain ⟨⟨l', hl'P⟩, hl'L, rfl⟩ := hy'
    have hlL' : l ∈ L := Subgroup.mem_subgroupOf.mp hlL
    have hl'L' : l' ∈ L' := Subgroup.mem_subgroupOf.mp hl'L
    have hz1 := I.map_eq_zBar hn hL (h8 L hL) hLl hu
    have hz2 := I.map_eq_zBar hn hL' (h8 L' hL') hL'l hu'
    have hzinv : (zBar α hα)⁻¹ = zBar α hα := by
      have hsq : zBar α hα * zBar α hα = 1 := by
        rw [← hz1, ← map_mul, ← map_one I.φ]
        congr 1
        exact Subtype.ext hu.sq
      exact inv_eq_of_mul_eq_one_right hsq
    have hinjLL : ∀ m ∈ L, ∀ m' ∈ L', ∀ hmm : m * m' ∈ pSpan P,
        I.φ ⟨m * m', hmm⟩ = 1 → m * m' = 1 := by
      intro m hm m' hm' hmm h1
      have hmP : m ∈ pSpan P := le_pSpan hL hm
      have hm'P : m' ∈ pSpan P := le_pSpan hL' hm'
      have hsplit : I.φ ⟨m * m', hmm⟩ = I.φ ⟨m, hmP⟩ * I.φ ⟨m', hm'P⟩ := by
        rw [← map_mul]
        rfl
      rw [hsplit] at h1
      have hinv' : I.φ ⟨m, hmP⟩ = (I.φ ⟨m', hm'P⟩)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have hmt : I.φ ⟨m, hmP⟩ ∈ memBar α hα true := by
        rw [← hLl]
        exact ⟨⟨m, hmP⟩, Subgroup.mem_subgroupOf.mpr hm, rfl⟩
      have hmf : I.φ ⟨m, hmP⟩ ∈ memBar α hα false := by
        rw [hinv', ← hL'l]
        exact Subgroup.inv_mem _ ⟨⟨m', hm'P⟩, Subgroup.mem_subgroupOf.mpr hm', rfl⟩
      have hm'inv : I.φ ⟨m', hm'P⟩ = (I.φ ⟨m, hmP⟩)⁻¹ := by rw [hinv', inv_inv]
      rcases inf_memBar_true_false hn hmt hmf with h2 | h2
      · have hm1 : m = 1 := phi_injOn I.φ hn hL (h8 L hL) hLl hm L.one_mem
          (by rw [h2]; exact (map_one I.φ).symm)
        have hm'1 : m' = 1 := phi_injOn I.φ hn hL' (h8 L' hL') hL'l hm' L'.one_mem
          (by rw [hm'inv, h2, inv_one]; exact (map_one I.φ).symm)
        rw [hm1, hm'1, mul_one]
      · have hmu : m = u := phi_injOn I.φ hn hL (h8 L hL) hLl hm hu.mem (by rw [h2, hz1])
        have hm'u : m' = u' := phi_injOn I.φ hn hL' (h8 L' hL') hL'l hm' hu'.mem
          (by rw [hm'inv, h2, hzinv, hz2])
        rw [hmu, hm'u, ← huu]
        exact hu.sq
    have hnormBar : ∀ b : Bool, conjSub (mkQ n (ofPerm (carmichaelPerm j))) (memBar α hα b) =
        memBar α hα b := by
      intro b
      have hmem : ∃ b', ∀ y : AEQ n, y ∈ memBar α hα b ↔
          ∃ c ∈ Certificates.AE117.memLC (ι 0) (ι 1) (ι 2) (ι 3) b', mkQ n c = y := by
        cases b
        · exact ⟨b₂, hb₂⟩
        · exact ⟨b₁, hb₁⟩
      obtain ⟨b', hb'⟩ := hmem
      have hle : conjSub (mkQ n (ofPerm (carmichaelPerm j))) (memBar α hα b) ≤ memBar α hα b := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, hc, rfl⟩ := (hb' y).mp hy
        refine (hb' _).mpr ⟨_, conj_carmichael_memLC hij' ι rfl rfl rfl rfl b' hc, ?_⟩
        show mkQ n (ofPerm (carmichaelPerm j) * c * (ofPerm (carmichaelPerm j))⁻¹) = _
        rw [map_mul, map_mul, map_inv]
        rfl
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    have hnormM : ∀ M ∈ P, ∀ b : Bool, (M.subgroupOf (pSpan P)).map I.φ = memBar α hα b →
        conjSub ((x j : G)) M = M := by
      intro M hM b hMl
      apply hdet _ (hinv M hM _ (x j).2) M hM
      rw [← conjSub_subgroupOf, ← Generic.conjSub_map, hxI j, hMl, hnormBar b]
    set xj : G := (x j : G) with hxj
    have hxj3 : xj ^ 3 = 1 := by
      have := congrArg Subtype.val (hx3 j)
      rwa [Subgroup.coe_pow, Subgroup.coe_one] at this
    have hLn := hnormM L hL true hLl
    have hL'n := hnormM L' hL' false hL'l
    have hc1 : ∀ {M : Subgroup G}, conjSub xj M = M → ∀ m ∈ M, xj⁻¹ * m * xj ∈ M := by
      intro M hM m hm
      rw [← hM] at hm
      exact mem_conjSub_iff.mp hm
    have hc2 : ∀ {M : Subgroup G}, conjSub xj M = M → ∀ m ∈ M, xj * m * xj⁻¹ ∈ M := by
      intro M hM m hm
      rw [← hM]
      exact conj_mem_conjSub hm
    have hcube := cube_eq_of_comm hxj3 (hcomm _ (hc1 hLn l hlL') l' hl'L').symm
      (hcomm _ (hc2 hLn l hlL') l' hl'L').symm (hcomm _ (hc2 hLn l hlL') _ (hc1 hL'n l' hl'L')).symm
    set w : ↥(pSpan P) := ⟨l, hlP⟩ * ⟨l', hl'P⟩ with hw
    have hwI : I.φ w = mkQ n (ofPerm (carmichaelPerm i * carmichaelPerm j)) := by
      rw [hw, map_mul, hyy]
    have hci : mkQ n (ofPerm (carmichaelPerm i * carmichaelPerm j)) *
        (mkQ n (ofPerm (carmichaelPerm j)))⁻¹ = mkQ n (ofPerm (carmichaelPerm i)) := by
      rw [← ofPerm_mul, map_mul, mul_inv_cancel_right]
    have hwxI : I.φ (w * (x j)⁻¹) = mkQ n (ofPerm (carmichaelPerm i)) := by
      rw [map_mul, map_inv, hwI, hxI j, hci]
    have hmemL : l * (xj⁻¹ * l * xj) * (xj * l * xj⁻¹) ∈ L :=
      L.mul_mem (L.mul_mem hlL' (hc1 hLn l hlL')) (hc2 hLn l hlL')
    have hmemL' : l' * (xj⁻¹ * l' * xj) * (xj * l' * xj⁻¹) ∈ L' :=
      L'.mul_mem (L'.mul_mem hl'L' (hc1 hL'n l' hl'L')) (hc2 hL'n l' hl'L')
    have hcube1 : (w * (x j)⁻¹) ^ 3 = 1 := by
      have hval : (((w * (x j)⁻¹) ^ 3 : ↥(pSpan P)) : G) =
          (l * (xj⁻¹ * l * xj) * (xj * l * xj⁻¹)) * (l' * (xj⁻¹ * l' * xj) * (xj * l' * xj⁻¹)) := by
        rw [← hcube]
        rfl
      have hmP := ((w * (x j)⁻¹) ^ 3).2
      rw [hval] at hmP
      have hI1 : I.φ ⟨_, hmP⟩ = 1 := by
        have e : (⟨_, hmP⟩ : ↥(pSpan P)) = (w * (x j)⁻¹) ^ 3 := Subtype.ext hval.symm
        rw [e, map_pow, hwxI, ← map_pow, ofPerm_pow]
        have hc3 : carmichaelPerm i ^ 3 = 1 := by
          rw [← (carmichaelPerm_isThreeCycle i).orderOf]
          exact pow_orderOf_eq_one _
        rw [hc3, ofPerm_one, map_one]
      have := hinjLL _ hmemL _ hmemL' hmP hI1
      exact Subtype.ext (hval.trans this)
    have hwx : w * (x j)⁻¹ = x i := huniq i _ hwxI hcube1
    have hw2 : w ^ 2 = 1 := by
      have hval : ((w ^ 2 : ↥(pSpan P)) : G) = (l * l) * (l' * l') := by
        rw [Subgroup.coe_pow, pow_two]
        show l * l' * (l * l') = l * l * (l' * l')
        rw [mul_assoc l l' (l * l'), ← mul_assoc l' l l', ← hcomm l hlL' l' hl'L']
        group
      have hmP := (w ^ 2).2
      rw [hval] at hmP
      have hI1 : I.φ ⟨_, hmP⟩ = 1 := by
        have e : (⟨_, hmP⟩ : ↥(pSpan P)) = w ^ 2 := Subtype.ext hval.symm
        rw [e, map_pow, hwI, ← map_pow, ofPerm_pow]
        have hsq : (carmichaelPerm i * carmichaelPerm j) ^ 2 = 1 :=
          congrArg Subtype.val (carmichaelCycle_mul_sq i j hij)
        rw [hsq, ofPerm_one, map_one]
      have := hinjLL _ (L.mul_mem hlL' hlL') _ (L'.mul_mem hl'L' hl'L') hmP hI1
      exact Subtype.ext (hval.trans this)
    calc (x i * x j) ^ 2 = w ^ 2 := by rw [← hwx, inv_mul_cancel_right]
      _ = 1 := hw2
  obtain ⟨F, hF⟩ := exists_hom_carmichaelCycle hn3 x hx3 hrel
  refine ⟨F, fun σ => ?_⟩
  have hcomp : I.φ.comp F =
      (mkQ n).comp ((ofPermHom n).comp (alternatingGroup (Fin n)).subtype) := by
    refine MonoidHom.eq_of_eqOn_dense (closure_range_carmichaelCycle hn3) ?_
    rintro _ ⟨k, rfl⟩
    show I.φ (F (carmichaelCycle k)) = mkQ n (ofPerm (carmichaelPerm k))
    rw [hF]
    exact hxI k
  exact DFunLike.congr_fun hcomp σ

end Section

end CFSG.ClassicalInvolution.Q3.TC.Thin
