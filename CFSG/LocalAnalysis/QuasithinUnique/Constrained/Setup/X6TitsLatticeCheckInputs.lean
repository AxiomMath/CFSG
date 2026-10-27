module

public import CFSG.Sporadic.Schreier.TitsStabCheckInputs

public section

namespace CFSG.QuasithinUnique.Setup.X6.TitsLat
open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

@[expose] def titsSFlagArrs : Array (Array ℕ) :=
  (titsSWords.map fun w => wordArr 8775 titsTFlagArrs w).toArray

@[expose] def titsSFlagReps : Array ℕ :=
  #[0, 1, 2, 4, 6, 9, 13, 19, 26, 38, 51, 72, 99, 141, 194, 281, 315, 464]

@[expose] def titsSFlagForest : Array ℕ × Array ℕ × Array ℕ × Array ℕ :=
  orbitForest 8775 titsSFlagArrs titsSFlagReps

@[expose] def titsSFlagSizes : List ℕ :=
  [1, 2, 4, 8, 8, 16, 32, 64, 64, 128, 256, 512, 512, 1024, 1024, 2048, 1024, 2048]

@[expose] def titsFlagMergeReps : List ℕ :=
  [4, 6, 9, 13, 19, 26, 38, 51, 72, 99, 141, 194, 281, 315, 464]

end CFSG.QuasithinUnique.Setup.X6.TitsLat
