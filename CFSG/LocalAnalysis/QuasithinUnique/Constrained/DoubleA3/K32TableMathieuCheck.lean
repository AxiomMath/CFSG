module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieuData
public meta import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.K32TableMathieuData
public import Certificates.Certificate4121
public import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.M23.M23Group
public meta import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M22
public import CFSG.Sporadic.Schreier.M23
public meta import CFSG.Sporadic.Schreier.M23
public import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreCentral
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public meta import CFSG.Sporadic.Schreier.MathieuOddCoreWords

public section

namespace CFSG.QuasithinUnique.DoubleA3.K32Mathieu

open CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem m23_ord3_cover :
    repsOK 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (cosetOrderTables m23Certificate 1 3) (m23Rep3.map toTable) 60000 = true ∧
    repSizes 23 (pairTables m23PermA m23PermB) (pairTables m23PermA⁻¹ m23PermB⁻¹)
      (m23Rep3.map toTable) 60000 = [56672] ∧
    (m23Rep3.map toTable).all (ordTest 23 3) = true :=
  Certificates.certificate4121.1

theorem m23_ord3_cent :
    m23Cent3Q.check = true ∧ m23Cent3Q.orderCertificate = 180 ∧
    (m23Cent3Words.map (evalCodes [m23PermA, m23PermB])).all
      (fun h => commT 23 (toTable h) (toTable (m23Rep3.getD 0 1))) = true :=
  Certificates.certificate4121.2.1

theorem m22_ord3_cover :
    repsOK 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (cosetOrderTables m22Certificate 1 3) (m22Rep3.map toTable) 14000 = true ∧
    repSizes 22 (pairTables m22gA m22gB) (pairTables m22gA⁻¹ m22gB⁻¹)
      (m22Rep3.map toTable) 14000 = [12320] ∧
    (m22Rep3.map toTable).all (ordTest 22 3) = true :=
  Certificates.certificate4121.2.2.1

theorem m22_ord3_cent :
    m22Cent3Q.check = true ∧ m22Cent3Q.orderCertificate = 36 ∧
    (m22Cent3Words.map (evalCodes [m22gA, m22gB])).all
      (fun h => commT 22 (toTable h) (toTable (m22Rep3.getD 0 1))) = true :=
  Certificates.certificate4121.2.2.2

end CFSG.QuasithinUnique.DoubleA3.K32Mathieu
