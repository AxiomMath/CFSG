module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.TorusLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.BorelLocal
public import CFSG.LocalAnalysis.AGLEmbeddingD2.SeitzTitsThree
public import CFSG.Sporadic.Schreier.TitsCert
public import Certificates.Certificate19760
public import Certificates.Certificate19761
import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.Sporadic.Schreier.TitsAutD
import CFSG.Sporadic.Schreier.TitsOuter

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four CFSG.Sporadic.Schreier.Tits
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.AGLEmbedding.MaxD2
open Certificates.MaxD2Perm

section Certified

theorem tits_five_dArr_size (j : ℕ) : (titsDArr j).size = 1755 := by
  unfold titsDArr CFSG.Sporadic.Schreier.Tits.commArr
  unfold CFSG.Monster.B.Co2.Native.compA
  exact Array.size_ofFn

theorem tits_five_genArr_size {i : ℕ} (hi : i < 4) : (titsGenArrs[i]!).size = 1755 := by
  have : titsGenArrs[i]! = titsArr1755 i := by
    simp only [titsGenArrs, titsField1755]
    rw [getElem!_pos _ _ (by simpa using hi)]
    simp
  rw [this]
  unfold titsArr1755
  exact Array.size_ofFn

theorem rep_array_two {n : ℕ} {a b : Tab} {x y : Equiv.Perm (Fin n)} (ha : TabRep a x)
    (hb : TabRep b y) :
    ∀ j, TabRep ((#[a, b] : Array Tab).getD j (idTab n)) ([x, y].getD j 1) := by
  intro j
  rcases j with _ | _ | j
  · simpa using ha
  · simpa using hb
  · simpa using TabRep.idTab (n := n)

theorem rep_array_six {n : ℕ} {a b c d e f : Tab} {x y z w u v : Equiv.Perm (Fin n)}
    (ha : TabRep a x) (hb : TabRep b y) (hc : TabRep c z) (hd : TabRep d w) (he : TabRep e u)
    (hf : TabRep f v) :
    ∀ j, TabRep ((#[a, b, c, d, e, f] : Array Tab).getD j (idTab n))
      ([x, y, z, w, u, v].getD j 1) := by
  intro j
  rcases j with _ | _ | _ | _ | _ | _ | j
  · simpa using ha
  · simpa using hb
  · simpa using hc
  · simpa using hd
  · simpa using he
  · simpa using hf
  · simpa using TabRep.idTab (n := n)

theorem factorization_five_eq_two {n : ℕ} (h2 : 5 ^ 2 ∣ n) (h3 : ¬ 5 ^ 3 ∣ n) (h0 : n ≠ 0) :
    n.factorization 5 = 2 := by
  have hp : Nat.Prime 5 := by norm_num
  have h1 : 2 ≤ n.factorization 5 := (hp.pow_dvd_iff_le_factorization h0).1 h2
  have h2' : ¬ 3 ≤ n.factorization 5 := fun h => h3 ((hp.pow_dvd_iff_le_factorization h0).2 h)
  omega

theorem orderOf_two_zmod_five : orderOf ((2 : ℕ) : ZMod 5) = 5 - 1 := by
  rw [orderOf_eq_iff (by norm_num)]
  decide

theorem tits_five_tab_d {j : ℕ} (hj : j < 2) :
    TabRep (titsDArr j) (titsDGen j) :=
  ⟨tits_five_dArr_size j, fun i => titsDArr_rep hj i⟩

theorem tits_five_tab_a {i : ℕ} (hi : i < 4) :
    TabRep (titsGenArrs[i]!) (titsGen i) :=
  ⟨tits_five_genArr_size hi, fun x => titsGen_rep hi x⟩

theorem titsD_eq_closure_list :
    titsD = Subgroup.closure {g | g ∈ [titsDGen 0, titsDGen 1]} := by
  unfold titsD
  congr 1
  ext x
  simp [Fin.exists_fin_two, eq_comm]

theorem titsA_eq_closure_list : titsA = Subgroup.closure
    {g | g ∈ [titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3]} := by
  apply le_antisymm
  · unfold titsA
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    apply Subgroup.subset_closure
    fin_cases i <;> simp
  · rw [Subgroup.closure_le]
    intro g hg
    simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact titsDGen_mem_titsA 0
    · exact titsDGen_mem_titsA 1
    · exact titsGen_mem_titsA (by norm_num)
    · exact titsGen_mem_titsA (by norm_num)
    · exact titsGen_mem_titsA (by norm_num)
    · exact titsGen_mem_titsA (by norm_num)

theorem titsD_hS : ∀ j,
    TabRep (titsDData.gT.getD j (idTab 1755)) ([titsDGen 0, titsDGen 1].getD j 1) :=
  rep_array_two (tits_five_tab_d (by norm_num)) (tits_five_tab_d (by norm_num))

theorem titsA_hS : ∀ j,
    TabRep (titsAData.gT.getD j (idTab 1755))
      ([titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3].getD j 1) :=
  rep_array_six (tits_five_tab_d (by norm_num)) (tits_five_tab_d (by norm_num))
    (tits_five_tab_a (by norm_num)) (tits_five_tab_a (by norm_num))
    (tits_five_tab_a (by norm_num)) (tits_five_tab_a (by norm_num))

theorem tits_five_local_check_d : check titsDData = true :=
  Certificates.certificate19760

theorem tits_five_local_check_a : check titsAData = true :=
  Certificates.certificate19761

theorem tits_five_localData_d :
    ∃ R : Subgroup (Equiv.Perm (Fin 1755)), LocalData 5 3 2 6 titsD R := by
  have h := localData_of_check (S := [titsDGen 0, titsDGen 1]) (D := titsDData) rfl
    (by show Nat.Prime 5; norm_num) titsD_hS
    (by
      have h1 : [titsDGen 0, titsDGen 1].length = 2 := rfl
      have h2 : titsDData.gT.size = 2 := rfl
      rw [h1, h2])
    (by rw [← titsD_eq_closure_list]; exact card_titsD)
    ⟨4, 1, by show (1200 : ℕ) = 5 ^ 2 * (2 ^ 4 * 3 ^ 1); norm_num⟩ tits_five_local_check_d
  rwa [← titsD_eq_closure_list] at h

theorem tits_five_localData_a :
    ∃ R : Subgroup (Equiv.Perm (Fin 1755)), LocalData 5 3 2 6 titsA R := by
  have h := localData_of_check
    (S := [titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3]) (D := titsAData)
    rfl (by show Nat.Prime 5; norm_num) titsA_hS
    (by
      have h1 : [titsDGen 0, titsDGen 1, titsGen 0, titsGen 1, titsGen 2, titsGen 3].length = 6 :=
        rfl
      have h2 : titsAData.gT.size = 6 := rfl
      rw [h1, h2])
    (by rw [← titsA_eq_closure_list]; exact card_titsA)
    ⟨5, 1, by show (2400 : ℕ) = 5 ^ 2 * (2 ^ 5 * 3 ^ 1); norm_num⟩ tits_five_local_check_a
  rwa [← titsA_eq_closure_list] at h

end Certified

theorem eq_titsD_or_titsA
    {G : Subgroup (Equiv.Perm (Fin 1755))} (h1 : titsD ≤ G) (h2 : G ≤ titsA) :
    G = titsD ∨ G = titsA := by
  have hD := Subgroup.card_dvd_of_le h1
  have hA := Subgroup.card_dvd_of_le h2
  rw [card_titsD] at hD
  rw [card_titsA] at hA
  obtain ⟨c, hc⟩ := hD
  have hc2 : c ∣ 2 := by
    rw [hc] at hA
    have : 17971200 * c ∣ 17971200 * 2 := by simpa using hA
    exact (Nat.mul_dvd_mul_iff_left (by norm_num)).1 this
  rcases (Nat.dvd_prime Nat.prime_two).1 hc2 with rfl | rfl
  · left
    exact (Subgroup.eq_of_le_of_card_ge h1 (by rw [hc, card_titsD])).symm
  · right
    exact Subgroup.eq_of_le_of_card_ge h2 (by rw [hc, card_titsA])

section Embedding


theorem exists_embedding_tits {X : Type} [Group X] {K : Subgroup X} [K.Normal]
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (eS : K ≃* titsD) :
    ∃ θ : X →* Equiv.Perm (Fin 1755), Function.Injective θ ∧ titsD ≤ θ.range ∧
      θ.range ≤ titsA := by
  let φ : X →* titsA :=
    (titsConjEquiv.symm.toMonoidHom).comp
      ((MulAut.congr eS).toMonoidHom.comp (MulAut.conjNormal (H := K)))
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : MulAut.congr eS (MulAut.conjNormal (H := K) x) = 1 := by
      have := congrArg titsConjEquiv hx
      simpa [φ] using this
    have h2 : (MulAut.conjNormal (H := K) x) = 1 :=
      (MulAut.congr eS).injective (h1.trans (map_one (MulAut.congr eS)).symm)
    have hx' : x ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have h3 := congrArg Subtype.val (MulEquiv.congr_fun h2 ⟨k, hk⟩)
      rw [MulAut.conjNormal_apply] at h3
      have h4 : x * k * x⁻¹ = k := h3
      have h5 : x * k = k * x := by
        calc x * k = (x * k * x⁻¹) * x := by group
          _ = k * x := by rw [h4]
      exact h5.symm
    rw [hKc] at hx'
    exact Subgroup.mem_bot.1 hx'
  refine ⟨titsA.subtype.comp φ, titsA.subtype_injective.comp hφinj, ?_, ?_⟩
  · intro g hg
    refine ⟨((eS.symm ⟨g, hg⟩ : K) : X), ?_⟩
    have h : φ ((eS.symm ⟨g, hg⟩ : K) : X) = ⟨g, titsD_le_titsA hg⟩ := by
      apply titsConjEquiv.injective
      have hL : titsConjEquiv (φ ((eS.symm ⟨g, hg⟩ : K) : X)) = MulAut.congr eS
          (MulAut.conjNormal (H := K) ((eS.symm ⟨g, hg⟩ : K) : X)) := by
        simp [φ]
      rw [hL]
      apply MulEquiv.ext
      intro d'
      apply Subtype.ext
      show ((eS (MulAut.conjNormal (H := K) ((eS.symm ⟨g, hg⟩ : K) : X) (eS.symm d')) : titsD) :
        Equiv.Perm (Fin 1755)) = g * d' * g⁻¹
      have : (MulAut.conjNormal (H := K) ((eS.symm ⟨g, hg⟩ : K) : X) (eS.symm d')) =
          eS.symm ⟨g, hg⟩ * eS.symm d' * (eS.symm ⟨g, hg⟩)⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [this, map_mul, map_mul, map_inv]
      simp
    show ((φ ((eS.symm ⟨g, hg⟩ : K) : X) : titsA) : Equiv.Perm (Fin 1755)) = g
    rw [h]
  · rintro _ ⟨x, rfl⟩
    exact (φ x).2

theorem torusLocal_tits_sylow
    {X : Type} [Group X] [Finite X] {K : Subgroup X} [K.Normal]
    (hKc : Subgroup.centralizer (K : Set X) = ⊥) (eS : K ≃* titsD) (R : Sylow 5 X) :
    TorusLocal 5 (R : Subgroup X) := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨θ, hθ, hD, hA⟩ := exists_embedding_tits hKc eS
  let e1 : X ≃* θ.range := MonoidHom.ofInjective hθ
  rcases eq_titsD_or_titsA hD hA with h | h
  · obtain ⟨R₀, hR₀⟩ := tits_five_localData_d
    have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_five (by norm_num)
    refine torusLocal_sylow (e1.trans (MulEquiv.subgroupCongr h)) hT ?_ R
    rw [hT.1, card_titsD,
      factorization_five_eq_two (by norm_num) (by norm_num) (by norm_num)]
  · obtain ⟨R₀, hR₀⟩ := tits_five_localData_a
    have hT := torusLocal_of_localData hR₀ (by norm_num) orderOf_two_zmod_five (by norm_num)
    refine torusLocal_sylow (e1.trans (MulEquiv.subgroupCongr h)) hT ?_ R
    rw [hT.1, card_titsA,
      factorization_five_eq_two (by norm_num) (by norm_num) (by norm_num)]

end Embedding

section Local


theorem d2TorusLocalAt_tits (d : TauCeti.ValidLieTypeIndex) (hd : d.1 = .tits) :
    D2TorusLocalAt (.lie d) fun p => p = 5 := by
  intro X _ _ K hKn hKc ⟨e⟩ p hp R
  subst hp
  refine ⟨?_, ?_⟩
  · rw [card_outer_tits_of_mulEquiv d hd e]
    norm_num
  · obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
    simp only at hd
    subst hd
    obtain ⟨eS⟩ := titsModelEquiv K 2 1
      (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits ⟨hv, ⟨e⟩⟩)
    have : K.Normal := hKn
    exact torusLocal_tits_sylow hKc eS R

end Local

end CFSG.AGLEmbeddingD2
