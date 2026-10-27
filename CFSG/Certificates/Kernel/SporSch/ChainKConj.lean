module

public import CFSG.Certificates.Kernel.SporSch.ChainKPack
public import CFSG.Certificates.Kernel.SporSch.MOCChain
public import CFSG.Certificates.Kernel.Spor.RawOrbHead
public import CFSG.Certificates.Kernel.Spor.PK.PermOf
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Schreier.Enumeration
public import CFSG.Certificates.Kernel.Spor.PK.Perm.Inv

public section

namespace CFSG.KS.SporSch.MOC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Raw.Orb CFSG.KS.PK
open CFSG.Certificates CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.Th
open CFSG.Sporadic.Th.Native CFSG.Monster.B.Mathieu

variable {n w : Nat}

theorem length_cosetOrderTables_one (hn : n < 2 ^ 32) (Q : RawSchreierDatum n) {m : Nat}
    (hm : 0 < m) :
    (cosetOrderTables Q 1 m).length = (enumeration Q).countP fun h => decide (orderOf h = m) := by
  rw [(forall₂_cosetOrderTables hn Q 1 hm).length_eq, List.length_reverse,
    ← List.countP_eq_length_filter, List.countP_map]
  apply List.countP_congr
  intro g _
  simp

theorem cosetOrderTables_length_conj (hn : 1 ≤ n) (hn32 : n < 2 ^ 32)
    (gens : List (Equiv.Perm (Fin n))) (words words' : List (List ℤ)) {k k' : Nat}
    (base : Vector (Fin n) k) (base' : Vector (Fin n) k') (hb : base.toList.Nodup)
    (hb' : base'.toList.Nodup) (σ : Equiv.Perm (Fin n))
    (hV : ValidSchreier (certificate hn gens words base hb))
    (hV' : ValidSchreier (certificate hn (gens.map fun g => σ * g * σ⁻¹) words' base' hb'))
    {m : Nat} (hm : 0 < m) :
    (cosetOrderTables (certificate hn (gens.map fun g => σ * g * σ⁻¹) words' base' hb') 1
      m).length = (cosetOrderTables (certificate hn gens words base hb) 1 m).length := by
  set Q := certificate hn gens words base hb
  set Q' := certificate hn (gens.map fun g => σ * g * σ⁻¹) words' base' hb'
  rw [length_cosetOrderTables_one hn32 Q' hm, length_cosetOrderTables_one hn32 Q hm]
  have hcl : Subgroup.closure {g | g ∈ gens.map fun g => σ * g * σ⁻¹} =
      (Subgroup.closure {g | g ∈ gens}).map (MulAut.conj σ).toMonoidHom := by
    rw [MonoidHom.map_closure]
    congr 1
    ext x
    simp [MulAut.conj_apply]
  have hmem : ∀ g, g ∈ Q'.originalSubgroup ↔ σ⁻¹ * g * σ ∈ Q.originalSubgroup := by
    intro g
    rw [certificate_originalSubgroup, certificate_originalSubgroup, hcl, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hy
    · intro h
      exact ⟨σ⁻¹ * g * σ, h, by simp [MulAut.conj_apply, mul_assoc]⟩
  have hperm : ((enumeration Q).map fun g => σ * g * σ⁻¹).Perm (enumeration Q') := by
    refine (List.perm_ext_iff_of_nodup ((enumeration_nodup Q hV).map fun x y hxy => ?_)
      (enumeration_nodup Q' hV')).2 fun a => ?_
    · simpa using hxy
    · rw [List.mem_map, mem_enumeration_iff Q' hV', hmem]
      constructor
      · rintro ⟨g, hg, rfl⟩
        rw [mem_enumeration_iff Q hV] at hg
        simpa [mul_assoc] using hg
      · intro h
        exact ⟨σ⁻¹ * a * σ, (mem_enumeration_iff Q hV _).2 h, by group⟩
  rw [← hperm.countP_eq, List.countP_map]
  apply List.countP_congr
  intro g _
  have ho : orderOf (σ * g * σ⁻¹) = orderOf g := by
    have := orderOf_injective (MulAut.conj σ).toMonoidHom (MulAut.conj σ).injective g
    simpa [MulAut.conj_apply] using this
  simp [ho]

theorem chainK_count_conj {gens : List (Equiv.Perm (Fin n))} {words words' : List (List Int)}
    {k k' : Nat} {bv : Vector (Fin n) k} {bv' : Vector (Fin n) k'}
    {PS PSI LR TR TRI PS' PSI' LR' TR' TRI' : Nat → Nat} {kS BP NS CH kS' BP' NS' CH' : Nat}
    {σ : Equiv.Perm (Fin n)} (hn : 1 ≤ n) (hbs : bv.toList.Nodup) (hbs' : bv'.toList.Nodup)
    (hQ : ChainK n w gens words bv PS PSI LR TR TRI kS BP NS CH)
    (hQ' : ChainK n w (gens.map fun g => σ * g * σ⁻¹) words' bv' PS' PSI' LR' TR' TRI' kS' BP'
      NS' CH') {m : Nat} (hm : 0 < m) :
    (cosetOrderTables (certificate hn gens words bv hbs) 1 m).length =
      (cosetOrderTables (certificate hn (gens.map fun g => σ * g * σ⁻¹) words' bv' hbs') 1
        m).length :=
  (cosetOrderTables_length_conj hn (lt_of_lt_of_le hQ.2.2.1 (by norm_num)) gens words words' bv
    bv' hbs hbs' σ (chainK_check hn hbs hQ).1 (chainK_check hn hbs' hQ').1 hm).symm

theorem prep_permOf {P Q : Nat} (h : permOK n w (mask w) (n * w) P Q = true) :
    PRep n w P (permOf n fun i => pg w (mask w) P i) ∧
      PRep n w Q (permOf n fun i => pg w (mask w) P i)⁻¹ := by
  obtain ⟨-, -, h3⟩ := permOK_facts h
  have hf : IsPermN n fun i => pg w (mask w) P i :=
    ⟨fun i hi => (h3 i hi).1, fun a ha b hb e => by
      have e' : pg w (mask w) P a = pg w (mask w) P b := e
      rw [← (h3 a ha).2, ← (h3 b hb).2, e']⟩
  have hp : PRep n w P (permOf n fun i => pg w (mask w) P i) := fun x => (permOf_apply hf x).symm
  exact ⟨hp, prep_inv_of_permOK hp h⟩

theorem conj_img (hn : n < 2 ^ 32) {gens : List (Equiv.Perm (Fin n))} {PS PC : Nat → Nat}
    {S SI : Nat} {σ : Equiv.Perm (Fin n)} (hS : PRep n w S σ) (hSI : PRep n w SI σ⁻¹)
    (himg : ∀ j < gens.length, imageList (gens.getD j 1) = (unpack n w (PS j)).toList)
    (hk : allN gens.length (fun j => Nat.beq (pcomp n w (mask w) S (pcomp n w (mask w) (PS j) SI))
      (PC j)) = true) :
    ∀ j < (gens.map fun g => σ * g * σ⁻¹).length,
      imageList ((gens.map fun g => σ * g * σ⁻¹).getD j 1) = (unpack n w (PC j)).toList := by
  intro j hj
  rw [List.length_map] at hj
  have e : (gens.map fun g => σ * g * σ⁻¹).getD j 1 = σ * (gens.getD j 1 * σ⁻¹) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map,
      List.getD_eq_getElem _ _ hj, mul_assoc]
  rw [e, ← Nat.eq_of_beq_eq_true (Orb.allN_iff.1 hk j hj)]
  exact imageList_of_prep (prep_pcomp hn hS (prep_pcomp hn (prep_of_imageList (himg j hj)) hSI))

end CFSG.KS.SporSch.MOC

end
