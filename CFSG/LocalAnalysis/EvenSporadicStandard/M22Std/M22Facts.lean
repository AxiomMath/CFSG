module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M22Std.TabGroup
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreClasses
public import CFSG.Sporadic.Mathieu.M22
public import Certificates.Certificate2195
public import Certificates.Certificate2202
public import CFSG.Sporadic.Schreier.MathieuOddCoreModel

public section

namespace CFSG.EvenSporadicStandard.M22Std

open CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.Certificates CFSG.Sporadic.Schreier
  CFSG.Sporadic.Mathieu CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

@[expose] def mkM22 (x : Equiv.Perm (Fin 22)) (hx : x ∈ NativeSporadic.M22) : Carrier .M22 :=
  (⟨x, hx⟩ : NativeSporadic.M22)

theorem toPerm_mkM22 (x : Equiv.Perm (Fin 22)) (hx : x ∈ NativeSporadic.M22) :
    toPerm (mkM22 x hx) = x := rfl

theorem toPerm_injective : Function.Injective toPerm := fun _ _ h => Subtype.ext h

theorem orderOf_toPerm (g : Carrier .M22) : orderOf (toPerm g) = orderOf g :=
  Subgroup.orderOf_coe (show NativeSporadic.M22 from g)

theorem m22Rep1_mem : m22Rep1 ∈ NativeSporadic.M22 := by
  obtain ⟨hr1, -⟩ := m22_rep_data1
  rwa [m22Certificate_originalSubgroup] at hr1

@[expose] noncomputable def rep1 : Carrier .M22 :=
  mkM22 m22Rep1 m22Rep1_mem

theorem m22_involution_conj :
    ∀ u : Carrier .M22, orderOf u = 2 → ∃ c : Carrier .M22, u = c * rep1 * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨hok, -, -⟩ := m22_oddcore_cover
  rw [m22InvReps_eq] at hok
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  obtain ⟨hr1, hro1, -⟩ := m22_rep_data1
  have h := (exists_conj_of_repsOK hn m22Certificate m22Certificate_check
    (pairTables_spec hn hA hB) 1 (fun h hh => by rw [inv_one, one_mul, mul_one]; exact hh)
    (by norm_num) [m22Rep1] (fun r hr => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      subst hr
      exact ⟨by simpa using hr1, hro1⟩) 2000 hok).1
  rw [m22Certificate_originalSubgroup] at h
  intro u hu
  obtain ⟨r, hr, c, hc, hcu⟩ := h (toPerm u) (show NativeSporadic.M22 from u).2
    (by rw [orderOf_toPerm]; exact hu)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact ⟨mkM22 c hc, toPerm_injective hcu⟩

theorem m22_involution_isSq
    {u : Carrier .M22} (hu : orderOf u = 2) : ∃ s : Carrier .M22, s * s = u := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  obtain ⟨-, hob, -⟩ := m22_word_orders
  have hb : orderOf m22gB = 4 :=
    (ordTest_iff perm_faithful (rep_toTable hn _) (by norm_num)).1 hob
  have hbb : orderOf (genB * genB) = 2 := by
    rw [← orderOf_toPerm, map_mul]
    change orderOf (m22gB * m22gB : Equiv.Perm (Fin 22)) = 2
    rw [← pow_two, orderOf_pow' _ (by norm_num : (2 : ℕ) ≠ 0), hb]
    norm_num
  obtain ⟨c, hc⟩ := m22_involution_conj u hu
  obtain ⟨d, hd⟩ := m22_involution_conj (genB * genB) hbb
  refine ⟨c * d⁻¹ * genB * d * c⁻¹, ?_⟩
  calc c * d⁻¹ * genB * d * c⁻¹ * (c * d⁻¹ * genB * d * c⁻¹)
      = c * (d⁻¹ * (genB * genB) * d) * c⁻¹ := by group
    _ = c * (d⁻¹ * (d * rep1 * d⁻¹) * d) * c⁻¹ := by rw [← hd]
    _ = c * rep1 * c⁻¹ := by group
    _ = u := hc.symm

end CFSG.EvenSporadicStandard.M22Std
