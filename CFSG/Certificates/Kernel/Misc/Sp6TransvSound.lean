module

public import CFSG.Certificates.Kernel.Sp62Pk.Sound
public import CFSG.Certificates.Kernel.Misc.PermClosSound
public import CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

public section

namespace CFSG.KC.Misc.Sp6Transv

open CFSG.KD.Sp62 CFSG.KC.Sp62 CFSG.KC.Misc.Clos CFSG.Quasithin.G2U
  CFSG.RankThree.PartTwo.Census.Carrier.Sp6Two

@[expose] def code6 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : List ℕ :=
  List.ofFn fun t : Fin 36 => (M ⟨t / 6, by omega⟩ ⟨t % 6, by omega⟩).val

@[expose] def enc6 (g : H6) : ℕ := pk (code6 (mat6 g))

theorem canon6_code6 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : canon6 (code6 M) = true := by
  simp only [canon6, code6, Bool.and_eq_true, beq_iff_eq, List.length_ofFn, List.all_eq_true,
    decide_eq_true_eq, true_and, List.mem_ofFn]
  rintro _ ⟨t, rfl⟩
  exact ZMod.val_lt _

theorem dec6_code6 (M : Matrix (Fin 6) (Fin 6) (ZMod 2)) : dec6 (code6 M) = M := by
  ext i j
  have hij : 6 * (i : ℕ) + j < (code6 M).length := by
    simp only [code6, List.length_ofFn]
    omega
  simp only [dec6, Matrix.of_apply]
  rw [List.getD_eq_getElem _ _ hij]
  simp only [code6, List.getElem_ofFn]
  have h1 : (⟨(6 * (i : ℕ) + j) / 6, by omega⟩ : Fin 6) = i := Fin.ext (by simp only; omega)
  have h2 : (⟨(6 * (i : ℕ) + j) % 6, by omega⟩ : Fin 6) = j := Fin.ext (by simp only; omega)
  rw [h1, h2, ZMod.natCast_val, ZMod.cast_id', id]

theorem code6_of {c : List ℕ} (hc : canon6 c = true) : code6 (dec6 c) = c :=
  dec6_injective (canon6_code6 _) hc (dec6_code6 _)

theorem enc6_of {g : H6} {c : List ℕ} (hg : mat6 g = dec6 c) (hc : canon6 c = true) :
    enc6 g = pk c := by
  rw [enc6, hg, code6_of hc]

theorem enc6_lt (g : H6) : enc6 g < 2 ^ 36 := canon_lt (canon6_code6 _)

theorem enc6_enc : ClosEnc enc6 MULF ONE where
  enc_one := by
    rw [enc6_of (by rw [map_one, dec6_one6]) canon6_one6, pk_one6]
  enc_mul a b := by
    have ha := canon6_code6 (mat6 a)
    have hb := canon6_code6 (mat6 b)
    rw [enc6_of (c := mul6 (code6 (mat6 a)) (code6 (mat6 b)))
      (by rw [map_mul, dec6_mul6, dec6_code6, dec6_code6]) (canon6_mul6 _ _), pk_mul6 ha hb]
    rfl
  inj a b h := by
    apply mat6_injective
    rw [← dec6_code6 (mat6 a), ← dec6_code6 (mat6 b),
      pk_inj (canon6_code6 _) (canon6_code6 _) h]

end CFSG.KC.Misc.Sp6Transv

end
