module

public import Certificates.Certificate17037

public section

namespace CFSG.QuasithinUnique.A5

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.DoubleA3
  CFSG.QuasithinUnique.A5.Delta5 CFSG.QuasithinUnique.A5.Action CFSG.QuasithinUnique.A5.Split
  Equiv

theorem dmul : ∀ x y : DihedralGroup 4, rmul (dtab x) (dtab y) = dtab (x * y) :=
  Certificates.certificate17037.1

theorem dtab_one : dtab 1 = rone :=
  Certificates.certificate17037.2.1

theorem dihedral4_pow : ∀ d : DihedralGroup 4, d ^ 4 = 1 :=
  Certificates.certificate17037.2.2.1

theorem pmul : ∀ x y : Perm (Fin 4), rmul (ptab x) (ptab y) = ptab (x * y) :=
  Certificates.certificate17037.2.2.2.1

theorem ptab_one : ptab 1 = rone :=
  Certificates.certificate17037.2.2.2.2.1

theorem dpcomm : ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rmul (ptab s) (dtab d) :=
  Certificates.certificate17037.2.2.2.2.2.1

theorem dtab_fix : ∀ d : DihedralGroup 4, pact (dtab d).2 g1 = g1 ∧ isEven (dtab d).1 :=
  Certificates.certificate17037.2.2.2.2.2.2.1

theorem ptab_fix : ∀ s : Perm (Fin 4), pact (ptab s).2 g1 = g1 ∧ isEven (ptab s).1 :=
  Certificates.certificate17037.2.2.2.2.2.2.2.1

theorem dp_kernel : ∀ (d : DihedralGroup 4) (s : Perm (Fin 4)),
    rmul (dtab d) (ptab s) = rone → d = 1 ∧ s = 1 :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.1

theorem dp_cover : ∀ v : Fin 5 → ZMod 2, isEven v → ∀ σ : Perm (Fin 5), pact σ g1 = g1 →
    ∃ (d : DihedralGroup 4) (s : Perm (Fin 4)), rmul (dtab d) (ptab s) = (v, σ) :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.1

theorem fix_A4 : ∀ v : Fin 5 → ZMod 2, isEven v →
    (∀ s : Perm (Fin 4), Perm.sign s = 1 → pact (ptab s).2 v = v) →
    v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1' :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.1

theorem fix_A4_mem : ∀ s : Perm (Fin 4), Perm.sign s = 1 →
    pact (ptab s).2 0 = 0 ∧ pact (ptab s).2 g1 = g1 ∧ pact (ptab s).2 gW1 = gW1 ∧
      pact (ptab s).2 gW1' = gW1' :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.1

theorem vecF_even : ∀ i, isEven (vecF i) :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vecF_mem : ∀ i, vecF i = 0 ∨ vecF i = g1 ∨ vecF i = gW1 ∨ vecF i = gW1' :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vecF_cover : ∀ v : Fin 5 → ZMod 2, (v = 0 ∨ v = g1 ∨ v = gW1 ∨ v = gW1') →
    ∃ i, vecF i = v :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem vecF_inj : ∀ i j, vecF i = vecF j → i = j :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem gW1_conj_z0 : ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1 :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem gW1'_conj_z0 : ∃ σ : Perm (Fin 5), Perm.sign σ = 1 ∧ pact σ z0 = gW1' :=
  Certificates.certificate17037.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.QuasithinUnique.A5
