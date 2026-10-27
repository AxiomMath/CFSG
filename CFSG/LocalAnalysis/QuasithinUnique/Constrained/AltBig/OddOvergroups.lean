module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddMain
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.OddFix
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AltBig.Final

public section

namespace CFSG.QuasithinUnique.L246C127.AltBig

open Equiv Equiv.Perm Subgroup CFSG.Open

theorem core_odd_overgroup {m : ℕ} (hm : 9 ≤ m) (hmodd : Odd m)
    {T X K : Subgroup ↥(alternatingGroup (Fin m))} (hT : CFSG.QuasithinUnique.IsSylowTwoOf T ⊤)
    (hTX : T ≤ X) (hKX : K ≤ X) (hsub : CFSG.Open.IsSubnormal K X)
    (hK : CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) :
    ∃ n, n ≤ m ∧ Nonempty (↥K ≃* alternatingGroup (Fin n)) := by
  rcases hK with hq | h3
  · obtain ⟨p, hTω, hp⟩ := exists_oddInv_of_sylow (α := Fin m) (by simpa using hmodd)
      (by simp; omega) hT
    by_cases hKω : ∀ k ∈ K, (k : Equiv.Perm (Fin m)) p.ω = p.ω
    · exact case_fix hm hmodd hT hTω hTX hKX hsub hq hKω
    · have hex : ∃ k ∈ K, (k : Equiv.Perm (Fin m)) p.ω ≠ p.ω := by
        by_contra hc
        apply hKω
        intro k hk
        by_contra h
        exact hc ⟨k, hk, h⟩
      obtain ⟨k₀, hk₀, hk₀ω⟩ := hex
      have hYA : X.map (alternatingGroup (Fin m)).subtype ≤ alternatingGroup (Fin m) := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hKY : K.map (alternatingGroup (Fin m)).subtype ≤
          X.map (alternatingGroup (Fin m)).subtype :=
        Subgroup.map_mono hKX
      have hB : p.Contained (X.map (alternatingGroup (Fin m)).subtype) :=
        fun x y h1 h2 h3 h4 => Subgroup.map_mono hTX (hp x y h1 h2 h3 h4)
      have hsub' : IsSubnormal (K.map (alternatingGroup (Fin m)).subtype)
          (X.map (alternatingGroup (Fin m)).subtype) :=
        CFSG.Quasithin.A3.subnormal_map (alternatingGroup (Fin m)).subtype hsub
      have hKe : ↥(K.map (alternatingGroup (Fin m)).subtype) ≃* ↥K :=
        (Subgroup.equivMapOfInjective K (alternatingGroup (Fin m)).subtype
          (alternatingGroup (Fin m)).subtype_injective).symm
      have hq' : CFSG.Open.IsQuasisimple ↥(K.map (alternatingGroup (Fin m)).subtype) :=
        open_isQuasisimple_of_mulEquiv hKe.symm
          (CFSG.Quasithin.B1Red.isQuasisimple_to_open hq)
      have hcomp : IsComponentOf (K.map (alternatingGroup (Fin m)).subtype)
          (X.map (alternatingGroup (Fin m)).subtype) := ⟨hKY, hsub', hq'⟩
      have hmove : ∃ e ∈ K.map (alternatingGroup (Fin m)).subtype, e p.ω ≠ p.ω :=
        ⟨(k₀ : Equiv.Perm (Fin m)), Subgroup.mem_map.2 ⟨k₀, hk₀, rfl⟩, hk₀ω⟩
      obtain ⟨k, -, hkm, ⟨ek⟩⟩ :=
        structure_component_odd p (by simpa using hm) (by simpa using hmodd) hYA hB hcomp hmove
      exact ⟨k, by simpa using hkm, ⟨hKe.symm.trans ek⟩⟩
  · refine ⟨3, by omega, ?_⟩
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact ⟨mulEquivOfPrimeCardEq h3 nat_card_alt_three⟩

end CFSG.QuasithinUnique.L246C127.AltBig

namespace CFSG.QuasithinUnique.L246C127

open CFSG.Open CFSG.Quasithin

theorem alt_overgroups_odd :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (L T X K : Subgroup Γ) (m : ℕ), 9 ≤ m → Odd m →
      Nonempty (↥L ≃* alternatingGroup (Fin m)) → IsSylowTwoOf T L → T ≤ X → X ≤ L → K ≤ X →
      IsSubnormal K X → (CFSG.IsQuasisimple ↥K ∨ Nat.card ↥K = 3) →
      ∃ n, n ≤ m ∧ IsAlt n ↥K := by
  intro Γ _ _ L T X K m hm hmodd hL hT hTX hXL hKX hsub hK
  obtain ⟨ψ⟩ := hL
  have hKL : K ≤ L := hKX.trans hXL
  have hsub1 : IsSubnormal (K.subgroupOf L) (X.subgroupOf L) :=
    A3.subnormal_comap L.subtype hsub
  have hsub2 : IsSubnormal ((K.subgroupOf L).map ψ.toMonoidHom)
      ((X.subgroupOf L).map ψ.toMonoidHom) :=
    A3.subnormal_map ψ.toMonoidHom hsub1
  have hT2 := isSylowTwoOf_top_map_subgroupOf ψ hT
  have hTX2 : (T.subgroupOf L).map ψ.toMonoidHom ≤ (X.subgroupOf L).map ψ.toMonoidHom :=
    Subgroup.map_mono (fun t ht => hTX ht)
  have hKX2 : (K.subgroupOf L).map ψ.toMonoidHom ≤ (X.subgroupOf L).map ψ.toMonoidHom :=
    Subgroup.map_mono (fun t ht => hKX ht)
  have eK : ↥((K.subgroupOf L).map ψ.toMonoidHom) ≃* ↥K :=
    (Subgroup.equivMapOfInjective (K.subgroupOf L) ψ.toMonoidHom ψ.injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe hKL)
  have hK2 : CFSG.IsQuasisimple ↥((K.subgroupOf L).map ψ.toMonoidHom) ∨
      Nat.card ↥((K.subgroupOf L).map ψ.toMonoidHom) = 3 := by
    rcases hK with hq | h3
    · exact Or.inl (CFSG.IsQuasisimple.of_mulEquiv eK hq)
    · exact Or.inr (by rw [Nat.card_congr eK.toEquiv]; exact h3)
  obtain ⟨n, hnm, ⟨e⟩⟩ := AltBig.core_odd_overgroup hm hmodd hT2 hTX2 hKX2 hsub2 hK2
  exact ⟨n, hnm, ⟨eK.symm.trans e⟩⟩

end CFSG.QuasithinUnique.L246C127
