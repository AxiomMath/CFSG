module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrLift
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P4S55BrPerf
public import CFSG.FeitThompson.OddOrderTheorem

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG
open scoped commutatorElement

section Lift

variable {A M Γ₀ : Type*} [Group A] [Finite A] [Group M] [Group Γ₀]

theorem solvable_normal_map_ker (ν : A →* M) (hνodd : Odd (Nat.card ν.ker)) (π : A →* Γ₀)
    (hπ : Function.Surjective π) :
    (ν.ker.map π).Normal ∧ Group.IsSolvable ↥(ν.ker.map π) := by
  refine ⟨Subgroup.Normal.map inferInstance π hπ, ?_⟩
  have hsol : Group.IsSolvable ↥ν.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hνodd
  exact Group.isSolvable_of_surjective (π.subgroupMap_surjective ν.ker)

theorem image_top_of_not_le {Lb W : Subgroup M} {Q : Type*} [Group Q] [IsSimpleGroup Q]
    (Φ : ↥Lb →* Q) (hΦs : Function.Surjective Φ) (hW : W.subgroupOf Lb = Φ.ker)
    {J : Subgroup M} (hJ : J.IsSubnormal) (hJL : J ≤ Lb) (hJW : ¬ J ≤ W) :
    (J.subgroupOf Lb).map Φ = ⊤ := by
  have hsn : ((J.subgroupOf Lb).map Φ).IsSubnormal :=
    (Subgroup.IsSubnormal.subgroupOf (K := Lb) hJ).map hΦs
  rcases hsn.eq_bot_or_top_of_isSimpleGroup inferInstance with h | h
  · exfalso
    apply hJW
    intro j hj
    have hjL : j ∈ Lb := hJL hj
    have hjm : (⟨j, hjL⟩ : ↥Lb) ∈ J.subgroupOf Lb := hj
    have h1 : Φ ⟨j, hjL⟩ = 1 := by
      have h2 : Φ ⟨j, hjL⟩ ∈ (J.subgroupOf Lb).map Φ := ⟨_, hjm, rfl⟩
      rw [h] at h2
      exact Subgroup.mem_bot.mp h2
    exact (mem_W_iff hW hjL).mpr h1
  · exact h

theorem recover_iso {Lb W : Subgroup M} {K : Subgroup Γ₀} (hK : IsQuasisimple ↥K)
    (Φ : ↥Lb →* ↥K ⧸ center ↥K) (hΦs : Function.Surjective Φ) (hW : W.subgroupOf Lb = Φ.ker)
    {J : Subgroup M} (hJ : IsComponent J) (hJL : J ≤ Lb) (hJW : ¬ J ≤ W) :
    Nonempty ((↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K)) := by
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
  have htop := image_top_of_not_le Φ hΦs hW hJ.2 hJL hJW
  let ΦJ : ↥J →* ↥K ⧸ center ↥K := Φ.comp (Subgroup.inclusion hJL)
  have hΦJs : Function.Surjective ΦJ := by
    intro q
    have hq : q ∈ (J.subgroupOf Lb).map Φ := by rw [htop]; trivial
    obtain ⟨j, hj, hjq⟩ := hq
    exact ⟨⟨(j : M), hj⟩, hjq⟩
  have hker1 : ΦJ.ker ≤ center ↥J := by
    rcases LocalCores.quasisimple_normal_subgroups hJ.1 (MonoidHom.normal_ker ΦJ) with h | h
    · exfalso
      obtain ⟨q, hq⟩ := exists_ne (1 : ↥K ⧸ center ↥K)
      obtain ⟨x, rfl⟩ := hΦJs q
      exact hq (MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x))
    · exact h
  have hker2 : center ↥J ≤ ΦJ.ker := by
    have hn : ((center ↥J).map ΦJ).Normal := Subgroup.Normal.map inferInstance ΦJ hΦJs
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((center ↥J).map ΦJ) with h | h
    · exact (Subgroup.map_eq_bot_iff _).mp h
    · exfalso
      obtain ⟨x, y, hxy⟩ := hK.2.2
      have hx : x ∈ (center ↥J).map ΦJ := by rw [h]; trivial
      have hy : y ∈ (center ↥J).map ΦJ := by rw [h]; trivial
      obtain ⟨z₁, hz₁, rfl⟩ := hx
      obtain ⟨z₂, hz₂, rfl⟩ := hy
      apply hxy
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz₂) z₁]
  have hker : center ↥J = ΦJ.ker := le_antisymm hker2 hker1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker).trans
    (QuotientGroup.quotientKerEquivOfSurjective ΦJ hΦJs)⟩

theorem recover (ν : A →* M) (π : A →* Γ₀) (hν : Function.Surjective ν) {K : Subgroup Γ₀}
    (hK : IsQuasisimple ↥K) (hDn : (ν.ker.map π).Normal) (hDs : Group.IsSolvable ↥(ν.ker.map π))
    (hKD : ⁅K, ν.ker.map π⁆ = ⊥) {L : Subgroup A} (hLK : L.map π = K) (hLle : L ≤ K.comap π)
    (Φ : ↥(L.map ν) →* ↥K ⧸ center ↥K) (hΦs : Function.Surjective Φ)
    (hΦ : ∀ (l : A) (hl : l ∈ L) (h : π l ∈ K),
      Φ ⟨ν l, Subgroup.mem_map_of_mem ν hl⟩ = QuotientGroup.mk ⟨π l, h⟩)
    {W : Subgroup M} (hW : W.subgroupOf (L.map ν) = Φ.ker) {J : Subgroup M} (hJ : IsComponent J)
    (hJL : J ≤ L.map ν) (hJW : ¬ J ≤ W) :
    (perfCore (J.comap ν)).map π = K ∧ Nonempty ((↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K)) := by
  refine ⟨?_, recover_iso hK Φ hΦs hW hJ hJL hJW⟩
  have := hDn
  have : IsSimpleGroup (↥K ⧸ center ↥K) := hK.2.1
  have hJperf : ⁅J, J⁆ = J := Subgroup.isPerfect_iff.mp hJ.1.1
  set Dl : Subgroup A := perfCore (J.comap ν) with hDl
  have hDlν : Dl.map ν = J := map_perfCore_comap_of_subnormal ν hν J hJ.2 hJperf
  have hDlperf : ⁅Dl, Dl⁆ = Dl := commutator_perfCore _
  have hX1 : Dl.map π ≤ K := by
    have hle1 : Dl ≤ (L.map ν).comap ν := (perfCore_le _).trans (Subgroup.comap_mono hJL)
    rw [Subgroup.comap_map_eq] at hle1
    have hle2 : Dl.map π ≤ ν.ker.map π ⊔ K :=
      calc Dl.map π ≤ (L ⊔ ν.ker).map π := Subgroup.map_mono hle1
        _ = L.map π ⊔ ν.ker.map π := Subgroup.map_sup _ _ _
        _ = ν.ker.map π ⊔ K := by rw [hLK, sup_comm]
    have hnorm : ν.ker.map π ≤ normalizer (K : Set Γ₀) := by
      refine le_trans ?_ (Subgroup.centralizer_le_normalizer (K : Set Γ₀))
      rw [Subgroup.commutator_comm] at hKD
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hKD
    have hperf : ⁅Dl.map π, Dl.map π⁆ = Dl.map π := by
      rw [← Subgroup.map_commutator, hDlperf]
    exact le_of_isPerfect_of_le_sup hDs hnorm hperf hle2
  have hX2 : ∀ k ∈ K, ∃ x ∈ Dl.map π, ∃ z ∈ Zsub K, k = x * z := by
    intro k hk
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp (hLK ▸ hk : k ∈ L.map π)
    have htop := image_top_of_not_le Φ hΦs hW hJ.2 hJL hJW
    have hq : (QuotientGroup.mk ⟨k, hk⟩ : ↥K ⧸ center ↥K) ∈
        (J.subgroupOf (L.map ν)).map Φ := by
      rw [htop]
      trivial
    obtain ⟨j, hj, hjq⟩ := hq
    have hjJ : (j : M) ∈ J := hj
    have hjDl : (j : M) ∈ Dl.map ν := by rw [hDlν]; exact hjJ
    obtain ⟨d, hd, hdj⟩ := hjDl
    obtain ⟨l₂, hl₂, hl₂j⟩ := Subgroup.mem_map.mp j.2
    have hπl₂ : π l₂ ∈ K := hLle hl₂
    have hΦj : Φ j = QuotientGroup.mk ⟨π l₂, hπl₂⟩ := by
      have hjeq : j = ⟨ν l₂, Subgroup.mem_map_of_mem ν hl₂⟩ := Subtype.ext hl₂j.symm
      rw [hjeq]
      exact hΦ l₂ hl₂ hπl₂
    have hdK : π d ∈ K := hX1 ⟨d, hd, rfl⟩
    have hker : d * l₂⁻¹ ∈ ν.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hdj, hl₂j, mul_inv_cancel]
    have hy : π d * (π l₂)⁻¹ ∈ ν.ker.map π := ⟨d * l₂⁻¹, hker, by simp⟩
    have hyK : π d * (π l₂)⁻¹ ∈ K := K.mul_mem hdK (K.inv_mem hπl₂)
    have hyZ : π d * (π l₂)⁻¹ ∈ Zsub K := mem_Zsub_of_comm hKD hyK hy
    have hz1 : (π l₂)⁻¹ * k ∈ Zsub K := by
      have hqq : (QuotientGroup.mk ⟨π l₂, hπl₂⟩ : ↥K ⧸ center ↥K) =
          QuotientGroup.mk ⟨k, hk⟩ := hΦj.symm.trans hjq
      exact mem_Zsub.mpr ⟨K.mul_mem (K.inv_mem hπl₂) hk, QuotientGroup.eq.mp hqq⟩
    have hyinv : (π d * (π l₂)⁻¹)⁻¹ ∈ Zsub K := (Zsub K).inv_mem hyZ
    have hcomm : π d * (π d * (π l₂)⁻¹)⁻¹ = (π d * (π l₂)⁻¹)⁻¹ * π d :=
      mul_comm_of_mem_Zsub hyinv hdK
    refine ⟨π d, ⟨d, hd, rfl⟩, (π d * (π l₂)⁻¹)⁻¹ * ((π l₂)⁻¹ * k),
      (Zsub K).mul_mem hyinv hz1, ?_⟩
    calc k = π l₂ * ((π l₂)⁻¹ * k) := by group
      _ = ((π d * (π l₂)⁻¹)⁻¹ * π d) * ((π l₂)⁻¹ * k) := by
          congr 1
          group
      _ = (π d * (π d * (π l₂)⁻¹)⁻¹) * ((π l₂)⁻¹ * k) := by rw [hcomm]
      _ = π d * ((π d * (π l₂)⁻¹)⁻¹ * ((π l₂)⁻¹ * k)) := by group
  exact eq_of_prod_Zsub hK hX1 hX2

theorem lift_setup [Finite Γ₀] (ν : A →* M) (π : A →* Γ₀) (hν : Function.Surjective ν)
    (hπ : Function.Surjective π) (hodd : Odd (Nat.card ν.ker)) {K : Subgroup Γ₀}
    (hK : IsComponent K) {a : A} (ha : π a ∈ normalizer (K : Set Γ₀))
    (hna : π a ∉ centralizer (K : Set Γ₀)) :
    ∃ Lb W : Subgroup M, Lb.IsSubnormal ∧ Group.IsPerfect ↥Lb ∧ ν a ∈ normalizer (Lb : Set M) ∧
      W ≤ Lb ∧ ν a ∈ normalizer (W : Set M) ∧
      ∃ _ : (W.subgroupOf Lb).Normal, IsSimpleGroup (↥Lb ⧸ W.subgroupOf Lb) ∧
        (∃ x y : ↥Lb ⧸ W.subgroupOf Lb, x * y ≠ y * x) ∧ (∃ l ∈ Lb, ⁅l, ν a⁆ ∉ W) ∧
        ∀ J : Subgroup M, IsComponent J → J ≤ Lb → ¬ J ≤ W →
          (perfCore (J.comap ν)).map π = K ∧
            Nonempty ((↥J ⧸ center ↥J) ≃* (↥K ⧸ center ↥K)) := by
  have : Group.IsPerfect ↥K := hK.1.1
  have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1.1
  set L : Subgroup A := perfCore (K.comap π) with hL
  have hLK : L.map π = K := map_perfCore_comap_of_subnormal π hπ K hK.2 hKperf
  have hLle : L ≤ K.comap π := perfCore_le _
  have hLperf : ⁅L, L⁆ = L := commutator_perfCore _
  have haL : a ∈ normalizer (L : Set A) := mem_normalizer_perfCore (mem_normalizer_comap π ha)
  obtain ⟨hDn, hDs⟩ := solvable_normal_map_ker ν hodd π hπ
  have hKD : ⁅K, ν.ker.map π⁆ = ⊥ :=
    (LocalCores.component_solvable_centralizer hDs hDn.isSubnormal).1 K hK
  let ψ : ↥L →* ↥K ⧸ center ↥K :=
    (QuotientGroup.mk' (center ↥K)).comp ((π.comp L.subtype).codRestrict K fun l => hLle l.2)
  have hψ : ∀ l : ↥L, ψ l = QuotientGroup.mk ⟨π l, hLle l.2⟩ := fun l => rfl
  have hker : ∀ l : ↥L, ν l = 1 → ψ l = 1 := by
    intro l hl
    have hl' : (l : A) ∈ ν.ker := hl
    have hZ : π l ∈ Zsub K := mem_Zsub_of_comm hKD (hLle l.2) ⟨l, hl', rfl⟩
    obtain ⟨_, hc⟩ := mem_Zsub.mp hZ
    rw [hψ]
    exact (QuotientGroup.eq_one_iff _).mpr hc
  obtain ⟨Φ, hΦ⟩ := exists_hom_map ν L ψ hker
  have hΦ' : ∀ (l : A) (hl : l ∈ L) (h : π l ∈ K),
      Φ ⟨ν l, Subgroup.mem_map_of_mem ν hl⟩ = QuotientGroup.mk ⟨π l, h⟩ :=
    fun l hl h => hΦ ⟨l, hl⟩
  have hΦs : Function.Surjective Φ := by
    intro q
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp (hLK ▸ hk : k ∈ L.map π)
    refine ⟨⟨ν l, Subgroup.mem_map_of_mem ν hl⟩, ?_⟩
    rw [hΦ' l hl (hLle hl)]
    congr 1
    exact Subtype.ext hlk
  obtain ⟨W, hWle, hW⟩ := exists_W (L.map ν) Φ
  have hWiff : ∀ l ∈ L, ν l ∈ W ↔ π l ∈ Zsub K := by
    intro l hl
    have hmem : ν l ∈ L.map ν := Subgroup.mem_map_of_mem ν hl
    rw [mem_W_iff hW hmem, hΦ' l hl (hLle hl)]
    constructor
    · intro h
      exact mem_Zsub.mpr ⟨hLle hl, (QuotientGroup.eq_one_iff _).mp h⟩
    · intro h
      exact (QuotientGroup.eq_one_iff _).mpr (mem_Zsub.mp h).2
  have conjW : ∀ b : A, b ∈ normalizer (L : Set A) → π b ∈ normalizer (K : Set Γ₀) →
      ∀ w ∈ W, ν b * w * (ν b)⁻¹ ∈ W := by
    intro b hbL hbK w hw
    obtain ⟨l, hl, hlw⟩ := Subgroup.mem_map.mp (hWle hw)
    have hwz : π l ∈ Zsub K := (hWiff l hl).mp (by rw [hlw]; exact hw)
    have hbl : b * l * b⁻¹ ∈ L := (mem_normalizer_iff.mp hbL l).mp hl
    have : ν (b * l * b⁻¹) ∈ W := (hWiff _ hbl).mpr (by simpa using conj_mem_Zsub hwz hbK)
    simpa [hlw] using this
  have hn : (W.subgroupOf (L.map ν)).Normal := by
    rw [hW]
    infer_instance
  have := hn
  obtain ⟨e⟩ := quot_equiv_of_eq Φ hΦs (W.subgroupOf (L.map ν)) hW
  have hsimple : IsSimpleGroup (↥(L.map ν) ⧸ W.subgroupOf (L.map ν)) :=
    e.isSimpleGroup_congr.mpr hK.1.2.1
  have hnonab : ∃ x y : ↥(L.map ν) ⧸ W.subgroupOf (L.map ν), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hK.1.2.2
    refine ⟨e.symm x, e.symm y, fun h => hxy ?_⟩
    have := congrArg e h
    simpa using this
  have hmove : ∃ l ∈ L.map ν, ⁅l, ν a⁆ ∉ W := by
    have hcomm : ∃ k ∈ K, ⁅k, π a⁆ ∉ Zsub K := by
      by_contra hcon
      exact hna (mem_centralizer_of_comm_mem_Zsub ha fun k hk => by
        by_contra hk'
        exact hcon ⟨k, hk, hk'⟩)
    obtain ⟨k, hk, hkZ⟩ := hcomm
    obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.mp (hLK ▸ hk : k ∈ L.map π)
    refine ⟨ν l, Subgroup.mem_map_of_mem ν hl, fun hW' => hkZ ?_⟩
    have hcl : ⁅l, a⁆ ∈ L := by
      rw [commutatorElement_def]
      have := (mem_normalizer_iff.mp haL l⁻¹).mp (L.inv_mem hl)
      simpa [mul_assoc] using L.mul_mem hl this
    have h1 := (hWiff _ hcl).mp (by simpa using hW')
    simpa [hlk] using h1
  refine ⟨L.map ν, W, ?_, ?_, mem_normalizer_map_br ν haL, hWle, ?_, hn, hsimple, hnonab, hmove,
    fun J hJ hJL hJW => recover ν π hν hK.1 hDn hDs hKD hLK hLle Φ hΦs hΦ' hW hJ hJL hJW⟩
  · exact (perfCore_isSubnormal (hK.2.comap π)).map hν
  · exact Subgroup.isPerfect_iff.mpr (by rw [← Subgroup.map_commutator, hLperf])
  · refine mem_normalizer_of_conj_mem (fun x hx => conjW a haL ha x hx) (fun x hx => ?_)
    have h1 := conjW a⁻¹ ((normalizer (L : Set A)).inv_mem haL)
      (by simpa using (normalizer (K : Set Γ₀)).inv_mem ha) x hx
    simpa using h1

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
